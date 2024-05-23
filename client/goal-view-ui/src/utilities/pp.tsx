import { FunctionComponent, ReactFragment, useRef, useState, useEffect, useLayoutEffect} from 'react';
import useResizeObserver from '@react-hook/resize-observer';
import {ResizeObserverEntry} from '@juggle/resize-observer';
import { PpString, PpMode } from '../types';
import PpBreak from './pp-break';
import PpBox from './pp-box';

import classes from './Pp.module.css';


type PpProps = {
    pp: PpString;
    coqCss: CSSModuleClasses;
};

type Box = {
    id: string,
    mode: PpMode;
    indent: number;
    depth: number;
    width: number;
    possibleBreaks: string[];
    breaks: string[];
};

type BreakInfo = {
    id: string,
    offset: number
};

type DisplayState = {
    breakIds: BreakInfo[];
    boxes: Box[];
};

const ppDisplay : FunctionComponent<PpProps> = (props) => {
    
    const {pp, coqCss} = props;

    const [maxBreaks, setMaxBreaks] = useState<number>(0);
    const [displayState, setDisplayState] = useState<DisplayState>({breakIds: [], boxes: []});
    const [lastEntry, setLastEntry] = useState<ResizeObserverEntry|null>(null);

    const container = useRef<HTMLDivElement>(null);
    const content = useRef<HTMLSpanElement>(null);

    useResizeObserver(container, (entry) => {
        
        if(container.current) {
            if(content.current) {
                //in this case the window has already been resized
                if(lastEntry) {

                    //don't trigger a recomputation for small resizes
                    if(Math.abs(entry.contentRect.width - lastEntry.contentRect.width) <= 10) {return;}
                    
                    //When we enlarge the window we should try and recompute boxes
                    if(entry.contentRect.width > lastEntry.contentRect.width) {
                        setDisplayState(ds => {
                            return {
                                breakIds: [],
                                boxes: ds.boxes.map(box => {
                                    return {...box, possibleBreaks: box.possibleBreaks.concat(box.breaks), breaks: []};
                                })
                            };
                        });
                    } else {
                        computeNeededBreaks(maxBreaks);
                    }
                } else {
                    computeNeededBreaks(maxBreaks);
                }
            }
        }
        setLastEntry(entry);
    });

    useEffect(() => {
        const breaks = computeNumBreaks(pp, 0);
        setMaxBreaks(breaks);
        setDisplayState({
            breakIds: [],
            boxes: getBoxes(pp, 0, 0, [])
        });
        computeNeededBreaks(breaks);
    }, [pp]);

    useLayoutEffect(() => {
        //computeBoxMargins();
        computeNeededBreaks(maxBreaks);
    }, [displayState]);

    const updateBoxWidth = (id: string, width: number) => {
        setDisplayState(ds => {
            return {
                ...ds,
                boxes: ds.boxes.map(b => {
                    if(b.id === id) {
                        return {...b, width: width};
                    }
                    return b;
                })
            };
        });
    };

    const computeBoxMargins = () => {
        if(content.current) {
            displayState.boxes.map(box => {
                if(box.depth = 0) {return;}
                const id = "box-" + box.id;
                const boxHtml = content.current!.querySelector(id);
                if(boxHtml) {
                    const prev = boxHtml.previousElementSibling;
                    if(prev) {
                        const rect = prev.getBoundingClientRect();
                        boxHtml.setAttribute('style', `marginLeft:${rect.left}`);
                    }
                    
                }
                return;
            });
        }
    };

    const computeNeededBreaks = (maxBreaks: number) => {
        if(container.current) {
            if(content.current) {
                const containerRect = container.current.getBoundingClientRect();
                const contentRect = content.current.getBoundingClientRect();
                if(containerRect.width < contentRect.width) {
                    if(displayState.breakIds.length < maxBreaks) {
                        checkBreaks(containerRect.width);
                    }
                }
            }
        }

    };

    const checkBreaks = (containerWidth: number) => {
        if(content.current) {
            let breakInfo : BreakInfo | null = null;
            let currBox : Element | null = null;
            const boxes = content.current.querySelectorAll("."+classes.Box);
            // const firstBox = displayState.boxes.length ? content.current.querySelector("#"+displayState.boxes[0].id) : null;
            // const initialOffset = firstBox ? firstBox.getBoundingClientRect().x : 0;
            for(let box of boxes) {
                const breaks = box.querySelectorAll(`:scope > :not(.${classes.Box}):not(.${classes.Tag}):not(.${classes.Text})`);
                for(let br of breaks) {
                    const breakId = br.id;
                    if(displayState.breakIds.find(info => info.id === breakId)) {continue; }

                    const next = br.nextElementSibling;
                    if(next && next.getBoundingClientRect().right > containerWidth) {
                        const parentBox = box.closest(`:not(#${box.id}).${classes.Box}`);
                        const parentOffset = parentBox ? parentBox.getBoundingClientRect().left : 0;
                        const offset = box.getBoundingClientRect().left - parentOffset;
                        breakInfo = {id: breakId, offset: offset};
                        break;
                    }
                }
                if(breakInfo) {
                    currBox = box;
                    break;
                }
            };

            if(breakInfo && currBox) {
                setDisplayState(ds => {
                    return {
                        breakIds: ds.breakIds.concat([breakInfo!]),
                        boxes: ds.boxes.map(b => {
                            if(b.id === currBox!.id) {
                                return {...b, breaks: b.breaks.concat([breakInfo!.id]), possibleBreaks: b.possibleBreaks.filter(id => id !== breakInfo!.id)};
                            }
                            return b;
                        })
                    };
                });
            }
        }
    };

    const getNextBreak = (containerWidth: number) => {
        if(displayState.boxes) {
            // Filter out the boxes that are saturated (all the breaks have been used)
            // The box widths are sorted by descending order => we always try to break the largest box first
            const candidateBoxes = displayState.boxes.filter(box => (box.width > containerWidth) && (box.possibleBreaks.length > 0));
            console.log("---------------------------------");
            console.log("ContainerWidth: ", containerWidth);
            console.log("BOXES:");
            console.log(candidateBoxes);
            console.log("---------------------------------");

            for(let i = 0; i < candidateBoxes.length; i++) {
                const box = candidateBoxes[i];
                //Ignore horizontal or vertical boxes
                if(box.mode === PpMode.horizontal) { continue; }
                else if (box.mode === PpMode.vertical) { continue; }
                //In the case of an hvbox trigger all breaks
                else if (box.mode === PpMode.hvBox) {
                    setDisplayState(ds => {
                        return {
                            breakIds: ds.breakIds.concat(box.possibleBreaks.map(id => {return {id: id, offset: 0}; })),
                            boxes: ds.boxes.map(b => {
                                if(b.id === box.id) {
                                    return {...box, breaks: box.possibleBreaks, possibleBreaks: []};
                                }
                                return b;
                            })
                        };
                    });
                }
                //Otherwise find the next breakId
                else {

                    setDisplayState(ds => {
                        return {
                            breakIds: ds.breakIds.concat([{id: box.possibleBreaks[0], offset: 0}]),
                            boxes: ds.boxes.map(b => {
                                if(b.id === box.id) {
                                    return {...b, breaks: box.breaks.concat([box.possibleBreaks[0]]), possibleBreaks: box.possibleBreaks.slice(1)};
                                }
                                return b;
                            })
                        };
                    });

                }

            }
        }
    };

    const computeNumBreaks = (pp: PpString, acc: number) : number => {
        switch(pp[0]) {
            case "Ppcmd_empty":
                return acc;
            case "Ppcmd_string":
                return acc;
            case "Ppcmd_glue":
                const nbBreaks = pp[1].map(pp => computeNumBreaks(pp, 0));
                const nb = nbBreaks.reduce((pv, cv) => {return pv + cv;}, 0);
                return acc + nb;
            case "Ppcmd_box":
            case "Ppcmd_tag":
                return computeNumBreaks(pp[2], acc);
            case "Ppcmd_print_break":
                return acc + 1;
            case "Ppcmd_force_newline":
                return acc;
            case "Ppcmd_comment":
                return acc;
        }
    };

    const getBoxBreaks = (pp: PpString, id: number, acc: string[]) : string[] => {
        switch(pp[0]) {
            case "Ppcmd_empty":
                return acc;
            case "Ppcmd_string":
                return acc;
            case "Ppcmd_glue":
                const nbBreaks = pp[1].map((pp, index) => getBoxBreaks(pp, id + index + 1 , []));
                const breaks = nbBreaks.reduce((pv, cv) => {return pv.concat(cv);}, []);
                return acc.concat(breaks);
            case "Ppcmd_box":
                return acc;
            case "Ppcmd_tag":
                return getBoxBreaks(pp[2], id + 1, acc);
            case "Ppcmd_print_break":
                return acc.concat(["break-"+id]);
            case "Ppcmd_force_newline":
                return acc;
            case "Ppcmd_comment":
                return acc;
        }
    };

    const getBoxes = (pp: PpString, id: number, depth: number, acc: Box[]) : Box[] => {
        switch(pp[0]) {
            case "Ppcmd_empty":
                return acc;
            case "Ppcmd_string":
                return acc;
            case "Ppcmd_glue":
                const boxes = pp[1].map((pp, index) => getBoxes(pp, id + index + 1, depth, []));
                return acc.concat(boxes.reduce((boxes, acc) => {return boxes.concat(acc); }));
            case "Ppcmd_box":
                const breaks = getBoxBreaks(pp[2], id + 1, []);
                const box = {
                    id: "box-"+id,
                    mode: pp[1][0],
                    indent: pp[1][1] ? pp[1][1] : 0,
                    depth: depth,
                    width: 0,
                    possibleBreaks: breaks,
                    breaks: []
                };
                return getBoxes(pp[2], id + 1, depth + 1, acc.concat([box]));
            case "Ppcmd_tag":
                return getBoxes(pp[2], id + 1, depth, acc);
            case "Ppcmd_print_break":
                return acc;
            case "Ppcmd_force_newline":
                return acc;
            case "Ppcmd_comment":
                return acc;
        }
    };

    return (
        <div ref={container} className={classes.Container}>
            <span ref={content} className={classes.Content}>
                {fragmentOfPpString(pp, coqCss, 0, displayState.breakIds, updateBoxWidth)}
            </span>
        </div>
    );

};


export const fragmentOfPpStringWithMode = (
    pp:PpString,
    mode: PpMode,
    coqCss:CSSModuleClasses,
    id: number,
    breakIds: BreakInfo[],
    indent:number = 0,
    updateBoxWidth: (id: string, width: number) => void,
) : ReactFragment => {
    switch (pp[0]) {
        case "Ppcmd_empty":
            return <></>;
        case "Ppcmd_string":
            return <span className={classes.Text}>{pp[1]}</span>;
        case "Ppcmd_glue":
            return pp[1].map((pp, index) => {
                return fragmentOfPpStringWithMode(pp, mode, coqCss, id + index + 1, breakIds, indent, updateBoxWidth);
            });
        case "Ppcmd_box":
            const m = pp[1][0];
            const i = (m !== PpMode.horizontal) ? pp[1][1] : 0;
            return (
                <PpBox 
                    pp={pp[2]} 
                    mode={m}
                    indent={i}
                    coqCss={coqCss}
                    recordWidth={updateBoxWidth}
                    id={id}
                    breaks={breakIds}
                />
            );
        case "Ppcmd_tag":
            return (
                <span className={[coqCss[pp[1].replaceAll(".", "-")], classes.Tag].join(' ')}>
                    {fragmentOfPpStringWithMode(pp[2], mode, coqCss, id + 1, breakIds, indent, updateBoxWidth)}
                </span>
            );
        case "Ppcmd_print_break":
            const br = breakIds.find(br => br.id === "break-"+id);
            return (
                <PpBreak
                    id={id}
                    offset={br ? br.offset : 0}
                    mode={mode}
                    horizontalIndent={pp[1]}
                    indent={indent}
                    lineBreak={br !== undefined}
                />
            );
        case "Ppcmd_force_newline":
            return <br/>;
        case "Ppcmd_comment":
            return pp[1];
    }
};

const fragmentOfPpString = (
    pp:PpString, coqCss:CSSModuleClasses,
    id: number,
    breakIds: BreakInfo[],
    updateBoxWidth: (id: string, width: number) => void
) : ReactFragment => {
    return fragmentOfPpStringWithMode(pp, PpMode.horizontal, coqCss, id, breakIds, 0, updateBoxWidth);
};

export default ppDisplay;