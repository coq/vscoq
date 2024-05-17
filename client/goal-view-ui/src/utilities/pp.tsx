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
    id: number,
    mode: PpMode;
    indent: number;
    depth: number;
    width: number;
    possibleBreaks: number[];
    breaks: number[];
};

const ppDisplay : FunctionComponent<PpProps> = (props) => {
    
    const {pp, coqCss} = props;

    const [maxBreaks, setMaxBreaks] = useState<number>(0);
    const [breakIds, setBreakIds] = useState<number[]>([]);
    const [boxes, setBoxes] = useState<Box[]>([]);
    const [saturatedBoxes, setSaturatedBoxes] = useState<number[]>([]);
    const [lastEntry, setLastEntry] = useState<ResizeObserverEntry|null>(null);

    const container = useRef<HTMLDivElement>(null);
    const content = useRef<HTMLSpanElement>(null);

    useResizeObserver(container, (entry) => {
        
        if(container.current) {
            if(content.current) {
                if(lastEntry) {
                    if(Math.abs(entry.contentRect.width - lastEntry.contentRect.width) <= 10) {return;}
                    
                    //When we enlarge the window we should try and recomputed boxes
                    if(entry.contentRect.width > lastEntry.contentRect.width) {
                        setBreakIds([]);
                        setBoxes(boxes => {
                            const newBoxes = boxes.map(box => {
                                return {...box, breaks: []};
                            });
                            return newBoxes;
                        });
                        setSaturatedBoxes([]);
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
        setBreakIds([]);
        setSaturatedBoxes([]);
        setBoxes(getBoxes(pp, 0, 0, []));
        computeNeededBreaks(breaks);
    }, [pp]);

    useLayoutEffect(() => {
        computeNeededBreaks(maxBreaks);
    });

    const updateBoxWidth = (id: number, width: number) => {

        setBoxes(boxes => {
            return boxes.map(b => {
                if(b.id === id) {
                    return {...b, width: width};
                }
                return b;
            }).sort((b1, b2) => {
                if(b1.depth !== b2.depth) {
                    return b1.depth - b2.depth;
                }
                else {
                    return b2.width - b1.width;
                }
                
            });
        });

    };

    const computeNeededBreaks = (maxBreaks: number) => {

        if(container.current) {
            if(content.current) {
                const containerRect = container.current.getBoundingClientRect();
                const contentRect = content.current.getBoundingClientRect();
                if(containerRect.width < contentRect.width) {
                    if(breakIds.length < maxBreaks) {
                        getNextBreak();
                    }
                }
            }
        }

    };

    const getNextBreak = () => {
        if(boxes) {
            // Filter out the boxes that are saturated (all the breaks have been used)
            // The box widths are sorted by descending order => we always try to break the largest box first
            const sortedBoxes = boxes.filter(box => !saturatedBoxes.find(id => id === box.id));

            for(let i = 0; i < sortedBoxes.length; i++) {
                const box = sortedBoxes[i];
                if(box && box.possibleBreaks) {
                    //Ignore horizontal or vertical boxes
                    if(box.mode === PpMode.horizontal) { continue; }
                    else if (box.mode === PpMode.vertical) { continue; }
                    //In the case of an hvbox trigger all breaks
                    else if (box.mode === PpMode.hvBox) {
                        setBreakIds(breakIds => {
                            return breakIds.concat(box.possibleBreaks);
                        });
                        setSaturatedBoxes(saturatedBoxes => {
                            return saturatedBoxes.concat([box.id]);
                        });
                        break;
                    }
                    //Otherwise find the next breakId
                    else {
                        const breakId = box.possibleBreaks.find((candidateId) => !breakIds.find(id => id === candidateId));
                        if(breakId) {
                            setBreakIds(breakIds => {
                                return breakIds.concat([breakId]);
                            });
                            const boxBreaks = box.breaks.concat([breakId]);
                            setBoxes(boxes => {
                                return boxes.map(b => {
                                    if(b.id === box.id) {
                                        return {...box, breaks: boxBreaks};
                                    }
                                    return b;
                                });
                            });
                            if(boxBreaks.length === box.possibleBreaks.length) {
                                setSaturatedBoxes(saturatedBoxes => {
                                    return saturatedBoxes.concat([box.id]);
                                });
                            }
                            break;
                        }

                    }

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

    const getBoxBreaks = (pp: PpString, id: number, acc: number[]) : number[] => {
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
                return acc.concat([id]);
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
                    id: id,
                    mode: pp[1][0],
                    indent: pp[1][1] ? pp[1][1] : 0,
                    depth: depth,
                    width: 0,
                    possibleBreaks: breaks, //.reverse(),
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
                {fragmentOfPpString(pp, coqCss, 0, breakIds, updateBoxWidth)}
            </span>
        </div>
    );

};


export const fragmentOfPpStringWithMode = (
    pp:PpString,
    mode: PpMode,
    coqCss:CSSModuleClasses,
    id: number,
    breakIds: number[],
    indent:number = 0,
    updateBoxWidth: (id: number, width: number) => void,
) : ReactFragment => {
    switch (pp[0]) {
        case "Ppcmd_empty":
            return <></>;
        case "Ppcmd_string":
            return pp[1];
        case "Ppcmd_glue":
            return pp[1].map((pp, index) => {
                return fragmentOfPpStringWithMode(pp, mode, coqCss, id + index + 1, breakIds, indent, updateBoxWidth);
            });
        case "Ppcmd_box":
            const m = pp[1][0];
            const i = (m !== PpMode.horizontal) ? pp[1][1] + indent : indent;
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
                <span className={coqCss[pp[1].replaceAll(".", "-")]}>
                    {fragmentOfPpStringWithMode(pp[2], mode, coqCss, id + 1, breakIds, indent, updateBoxWidth)}
                </span>
            );
        case "Ppcmd_print_break":
            const lineBreak = breakIds.find(breakId => breakId === id) !== undefined;
            return <PpBreak 
                mode={mode}
                horizontalIndent={pp[1]}
                indent={indent}
                lineBreak={lineBreak}
            />;
        case "Ppcmd_force_newline":
            return <br/>;
        case "Ppcmd_comment":
            return pp[1];
    }
};

const fragmentOfPpString = (
    pp:PpString, coqCss:CSSModuleClasses,
    id: number,
    breakIds: number[],
    updateBoxWidth: (id: number, width: number) => void
) : ReactFragment => {
    return fragmentOfPpStringWithMode(pp, PpMode.horizontal, coqCss, id, breakIds, 0, updateBoxWidth);
};

export default ppDisplay;