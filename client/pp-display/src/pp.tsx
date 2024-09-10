import { FunctionComponent, useRef, useState, useEffect, useLayoutEffect} from 'react';
import useResizeObserver from '@react-hook/resize-observer';
import {ResizeObserverEntry} from '@juggle/resize-observer';
import { v4 as uuid } from 'uuid';

import { PpString, PpMode, BoxDisplay, Term, Break, Box, DisplayType, BreakInfo, HideStates, Token, TokenType } from './types';
import PpBox from './pp-box';

import classes from './Pp.module.css';

type PpProps = {
    pp: PpString;
    coqCss: CSSModuleClasses;
    maxDepth: number;
};

type DisplayState = {
    breakIds: BreakInfo[];
    display: Box | null;
    tokenStream: Token[] | null;
    context: CanvasRenderingContext2D | null
};

const ppDisplay : FunctionComponent<PpProps> = (props) => {
    
    const {pp, coqCss, maxDepth} = props;
    const [displayState, setDisplayState] = useState<DisplayState>({breakIds: [], display: null, tokenStream: null, context: null});
    const [lastEntry, setLastEntry] = useState<ResizeObserverEntry|null>(null);
    const [hovered, setHovered] = useState<boolean>(false);
    useEffect(() => {
        window.addEventListener('keydown', onKeyDown);
        window.addEventListener('keyup', onKeyUp);
        return () => {
            window.removeEventListener('keydown', onKeyDown);
            window.removeEventListener('keyup', onKeyUp);
        };
    }, []);

    const onKeyDown = (e : KeyboardEvent) => {
        if(e.altKey) {
            setHovered(true);
        }
    };

    const onKeyUp = (_: KeyboardEvent) => {
        setHovered(false);
    };


    const container = useRef<HTMLDivElement>(null);
    const content = useRef<HTMLSpanElement>(null);
    //this ref prevents a recomputing loop when resizing
    const alreadyComputed = useRef<boolean>(false);

    useResizeObserver(container, (entry) => {
        
        if(container.current) {
            if(content.current) {
                //in this case the window has already been resized
                if(lastEntry) {
                    //don't trigger a recomputation for small resizes
                    if(Math.abs(entry.contentRect.width - lastEntry.contentRect.width) <= 10) {return;}
                }
                //setting the display state triggers the recomputation
                alreadyComputed.current = false;
                setDisplayState(ds => {
                    return {
                        ...ds,
                        breakIds: []
                    };
                });
            }
        }

        setLastEntry(entry);
    });

    useEffect(() => {
        intializeDisplay(pp);
    }, [pp]);

    useLayoutEffect(() => {
        if(!alreadyComputed.current) {
            alreadyComputed.current = true;
            computeNeededBreaks();
        }
    }, [displayState]);

    const intializeDisplay = (pp: PpString) => {
        if(content.current) {
            const context = getContext();
            context!.font = getComputedStyle(content.current).font || 'monospace' ;
            const display = boxifyPpString(pp);
            const tokenStream = buildTokenStream(display, context!);
            alreadyComputed.current = false;
            setDisplayState({
                breakIds: [],
                display: display,
                tokenStream: tokenStream,
                context: context
            });
        }
    };

    const getPpTag  = (pp: PpString, tag: string, indent: number, mode: PpMode, depth: number) => {
        const id = uuid();
        switch(pp[0]) {
            case 'Ppcmd_empty':
                console.error('Received PpTag with empty');
                return null;
            case 'Ppcmd_string':
                return {
                    type: DisplayType.term,
                    classList: [classes.Tag, tag],
                    content: pp[1]
                } as Term;
            case 'Ppcmd_glue':
                return {
                    id: "box-"+id,
                    type: DisplayType.box,
                    mode: mode,
                    classList: [tag],
                    indent: indent,
                    boxChildren: flattenGlue(pp[1], mode, indent, id, depth + 1)
                } as Box;
            case 'Ppcmd_force_newline':
                console.error('Received PpTag with fnl');
                return null;
            case 'Ppcmd_comment':
                console.error('Received PpTag with comment');
                return null;
            case 'Ppcmd_box':
                const m = pp[1][0];
                const i = (m !== PpMode.horizontal) ? pp[1][1] : 0;
                return {
                    id: "box-"+id,
                    type: DisplayType.box,
                    mode: mode,
                    classList: [tag],
                    indent: indent,
                    boxChildren: getBoxChildren(pp[2], m, i, id, depth + 1)
                } as Box;
            case 'Ppcmd_tag':
                console.error('Received PpTag with tag');
                return null;
            case 'Ppcmd_print_break':
                console.error('Received PpTag with br');
                return null;
        }
    };

    const flattenGlue = (glue: PpString[], mode: PpMode, indent: number, boxId: string, depth: number) : BoxDisplay[] => {

        const g = glue.map(pp => {
            switch(pp[0]) {
                case 'Ppcmd_empty':
                    return [];
                case 'Ppcmd_string':
                    return [{
                        type: DisplayType.term,
                        classList: [classes.Text],
                        content: pp[1]
                    } as Term];
                case 'Ppcmd_glue':
                        return flattenGlue(pp[1], mode, indent, boxId, depth);
                case 'Ppcmd_force_newline':
                    return [{
                        id: "fnl",
                        type: DisplayType.break,
                        offset: 0,
                        mode: mode,
                        horizontalIndent: 0, 
                        indent: indent,
                        shouldBreak: true,
                    } as Break];
                case 'Ppcmd_comment':
                    return [];
                case 'Ppcmd_box':
                    return [boxifyPpString(pp, depth)];
                case 'Ppcmd_tag':
                    return [getPpTag(pp[2], coqCss[pp[1].replaceAll(".", "-")], indent, mode, depth)];
                case 'Ppcmd_print_break':
                    const brId = uuid();
                    return [{
                        id: "box-"+boxId+"break-"+brId,
                        type: DisplayType.break,
                        offset: 0,
                        mode: mode,
                        horizontalIndent: pp[1],
                        indent: pp[2],
                        shouldBreak: false
                    } as Break];
            }
        });
        const r = g.reduce((acc, curr) => {
            return acc.concat(curr);
        }, []);

        return r;
    };

    const getBoxChildren = (pp : PpString, mode: PpMode, indent: number, boxId: string, depth: number) : BoxDisplay[] => {
        switch(pp[0]) {
            case "Ppcmd_empty":
                return [];
            case "Ppcmd_glue":
                return flattenGlue(pp[1], mode, indent, boxId, depth);
            case 'Ppcmd_string':
                return [{
                    type: DisplayType.term,
                    classList: [classes.Text],
                    content: pp[1]
                } as Term];
            case 'Ppcmd_force_newline':
                return [];
            case 'Ppcmd_comment':
                return [];
            case 'Ppcmd_box':
                return [
                    boxifyPpString(pp, depth)
                ];
            case 'Ppcmd_tag':
                return [
                    getPpTag(pp[2], coqCss[pp[1].replaceAll(".", "-")], indent, mode, depth)
                ];
            case 'Ppcmd_print_break':
                return [];
        }
    };

    const boxifyPpString = (pp : PpString, depth : number = 0) => {
        const id = uuid();
        switch (pp[0]) {
            case 'Ppcmd_empty':
            case 'Ppcmd_string':
            case 'Ppcmd_glue':
            case 'Ppcmd_force_newline':
            case 'Ppcmd_comment':
            case 'Ppcmd_tag':
            case 'Ppcmd_print_break':
                console.log('Goal contains non-boxed PpString');
                return {
                    id: "box-"+id,
                    type: DisplayType.box,
                    depth: depth,
                    classList: [],
                    mode: PpMode.hovBox,
                    indent: 0,
                    boxChildren: getBoxChildren(pp, PpMode.hovBox, 0, id, depth + 1)
                } as Box;
            case 'Ppcmd_box':
                const mode = pp[1][0];
                const indent = (mode !== PpMode.horizontal) ? pp[1][1] : 0;
                return {
                    id: "box-"+id,
                    type: DisplayType.box,
                    depth: depth,
                    mode: mode,
                    classList: [],
                    indent: indent,
                    boxChildren: getBoxChildren(pp[2], mode, indent, id, depth + 1)
                } as Box;
        }
    };

    const computeNeededBreaks = () => {
        if(container.current) {
            const containerRect = container.current.getBoundingClientRect();
            if(displayState.tokenStream && displayState.context) {
                scanTokenStream(displayState.tokenStream, containerRect.width, displayState.context);
            }
        }

    };

    //create a canvas and get its context to compute character width
    const getContext = ()  => {
        const fragment = document.createDocumentFragment();
        const canvas = document.createElement('canvas');
        fragment.appendChild(canvas);
        return canvas.getContext('2d');
    };

    const estimateBoxWidth = (box: Box, context: CanvasRenderingContext2D) : number => {
        let currentWidth = 0;
        for (let childBox of box.boxChildren) {
            if(childBox) {
                switch(childBox.type) {
                    case DisplayType.box:
                        currentWidth += estimateBoxWidth(childBox, context);
                        break;
                    case DisplayType.break:
                        break;
                    case DisplayType.term:
                        currentWidth += context.measureText(childBox.content).width;
                        break;
                }
            }
        }
        return currentWidth;
    };

    const scanTokenStream = (tokenStream: Token[], containerWidth: number, context: CanvasRenderingContext2D) => {
        let currentLineWidth = 0;
        let breakAll : boolean[] = [];
        let breaks : BreakInfo[] = [];
        let currentOffset : number[] = [0];
        for(let token of tokenStream) {
            switch(token.type) {
                case TokenType.term:
                    currentLineWidth += token.length;
                    break;
                case TokenType.open:
                    if((token.mode === PpMode.hvBox && currentLineWidth + token.length > containerWidth)
                        || token.mode === PpMode.vertical
                    ) {
                        breakAll.push(true);
                    } else {
                        breakAll.push(false);
                    }
                    currentOffset.push(token.offset + currentLineWidth);
                    break;
                case TokenType.close:
                    if(breakAll.length > 0) { breakAll.pop(); }
                    currentOffset.pop();
                    break;
                case TokenType.break:
                    if(currentLineWidth + token.length > containerWidth || breakAll[breakAll.length - 1]) {
                        const offset = currentOffset[currentOffset.length - 1];
                        breaks.push({id: token.id, offset: offset + token.indent});
                        currentLineWidth = offset + token.indent;
                        break;
                    }
                    currentLineWidth += context.measureText(" ").width;
                    break;
            }
        }
        setDisplayState(ds => {
            return {
                ...ds,
                breakIds: breaks
            };
        });
    };

    const buildTokenStream = (box: Box, context: CanvasRenderingContext2D) : Token[] => {
        let tokenStream : Token[] = [];
        for (let i = 0; i < box.boxChildren.length; i++) {
            let childBox = box.boxChildren[i];
            if(childBox) {
                switch(childBox.type) {
                    case DisplayType.box:
                        const blockWidth = estimateBoxWidth(childBox, context);
                        const blockTokenStream = buildTokenStream(childBox, context);
                        const offset = context.measureText(" ".repeat(childBox.indent)).width;
                        tokenStream = tokenStream.concat([{type: TokenType.open, length: blockWidth, mode: childBox.mode, offset: offset}])
                                             .concat(blockTokenStream)
                                             .concat([{type: TokenType.close}]);
                        break;
                    case DisplayType.break:
                        let blockLength = 0;
                        for(let j = i + 1; j < box.boxChildren.length; j++) {
                            let nextBlock = box.boxChildren[j];
                            if(nextBlock) {
                                switch(nextBlock.type) {
                                    case DisplayType.box:
                                        blockLength += estimateBoxWidth(nextBlock, context);
                                        break;
                                    case DisplayType.break:
                                        break;
                                    case DisplayType.term:
                                        blockLength += context.measureText(nextBlock.content).width;
                                }
                                if(nextBlock.type === DisplayType.break) {
                                    break;
                                }
                            }
                        }
                        const indent = context.measureText(" ").width * childBox.indent;
                        tokenStream = tokenStream.concat([{type: TokenType.break, id: childBox.id, length: blockLength, indent: indent}]);
                        break;
                    case DisplayType.term:
                        tokenStream = tokenStream.concat({type: TokenType.term, length: context.measureText(childBox.content).width});
                        break;
                }
            }
        }
        return tokenStream;
    };

    return (
        <div ref={container} className={classes.Container}>
            <span ref={content} className={classes.Content}>
                {
                    displayState.display ?
                    <PpBox
                        id={displayState.display.id}
                        coqCss={coqCss}
                        depth={0}
                        parentHide={HideStates.UNHIDE}
                        hovered={hovered}
                        maxDepth={maxDepth}
                        classList={[]}
                        mode={displayState.display.mode}
                        type={displayState.display.type}
                        boxChildren={displayState.display.boxChildren}
                        indent={displayState.display.indent}
                        breaks={displayState.breakIds}
                        addedDepth={0}
                    />
                    : null
                }
            </span>
        </div>
    );

};


export default ppDisplay;