import { FunctionComponent, ReactFragment, useRef, useState, useEffect, useLayoutEffect } from 'react';
import useResizeObserver from '@react-hook/resize-observer';
import {ResizeObserverEntry} from '@juggle/resize-observer';
import { PpString, PpMode } from '../types';
import PpBreak from './pp-break';

import classes from './Pp.module.css';


type PpProps = {
    pp: PpString;
    coqCss: CSSModuleClasses;
};

const ppDisplay : FunctionComponent<PpProps> = (props) => {
    
    const {pp, coqCss} = props;

    const [maxBreaks, setMaxBreaks] = useState<number>(0);
    const [neededBreaks, setNeededBreaks] = useState<number>(0);
    const [possibleBreakIds, setPossibleBreakIds] = useState<number[]>([]);
    const [breakIds, setBreakIds] = useState<number[]>([]);
    const [lastEntry, setLastEntry] = useState<ResizeObserverEntry|null>(null);
    const container = useRef<HTMLDivElement>(null);
    const content = useRef<HTMLSpanElement>(null);

    useResizeObserver(container, (entry) => {
        
        if(container.current) {
            if(content.current) {
                if(lastEntry) {
                    if(Math.abs(entry.contentRect.width - lastEntry.contentRect.width) <= 10) {return;}
                    console.log("ENTRIES: " + entry.contentRect.width + ", " + lastEntry.contentRect.width);
                    if(entry.contentRect.width > lastEntry.contentRect.width) {
                        setNeededBreaks(0);
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
        computeNeededBreaks(maxBreaks);
        setMaxBreaks(computeNumBreaks(pp, 0));
        getBreakIds(pp, 0);
    }, []);

    useEffect(() => {
        setBreakIds(possibleBreakIds.slice(0, neededBreaks));
    }, [neededBreaks]);

    useLayoutEffect(() => {
        computeNeededBreaks(maxBreaks);
    });

    const computeNeededBreaks = (maxBreaks: number) => {

        if(container.current) {
            if(content.current) {
                const containerRect = container.current.getBoundingClientRect();
                const contentRect = content.current.getBoundingClientRect();
                console.log("container width: " + containerRect.width);
                console.log("content width: " + contentRect.width);
                if(containerRect.width < contentRect.width) {
                    if(neededBreaks < maxBreaks) {
                        console.log("Setting needed breaks: " + (neededBreaks + 1));
                        setNeededBreaks((neededBreaks) => {return neededBreaks + 1;});
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

    const getBreakIds = (pp: PpString, id: number) => {
        switch(pp[0]) {
            case "Ppcmd_empty":
                return;
            case "Ppcmd_string":
                return;
            case "Ppcmd_glue":
                pp[1].map((pp, index) => getBreakIds(pp, id + index + 1));
                return;
            case "Ppcmd_box":
            case "Ppcmd_tag":
                getBreakIds(pp[2], id + 1);
                return;
            case "Ppcmd_print_break":
                setPossibleBreakIds((possibleBreakIds) => {
                    return possibleBreakIds.concat([id]);
                });
                return;
            case "Ppcmd_force_newline":
                return;
            case "Ppcmd_comment":
                return;
        }
    };

    console.log("NEEDED BREAKS: " + neededBreaks);
    return (
        <div ref={container} className={classes.Container}>
            <span ref={content} className={classes.Content}>
                {fragmentOfPpString(pp, coqCss, 0, breakIds)}
            </span>
        </div>
    );

};


const fragmentOfPpStringWithMode = (
    pp:PpString,
    mode: PpMode,
    coqCss:CSSModuleClasses,
    id: number,
    breakIds: number[],
    indent:number = 0
) : ReactFragment => {
    switch (pp[0]) {
        case "Ppcmd_empty":
            return <></>;
        case "Ppcmd_string":
            return pp[1];
        case "Ppcmd_glue":
            return pp[1].map((pp, index) => {
                return fragmentOfPpStringWithMode(pp, mode, coqCss, id + index + 1, breakIds, indent);
            });
        case "Ppcmd_box":
            const m = pp[1][0];
            const i = (m !== PpMode.horizontal) ? pp[1][1] : 0;
            return (
                fragmentOfPpStringWithMode(pp[2], m, coqCss, id + 1, breakIds, i + indent)
            );
        case "Ppcmd_tag":
            return (
                <span className={coqCss[pp[1].replaceAll(".", "-")]}>
                    {fragmentOfPpStringWithMode(pp[2], mode, coqCss, id + 1, breakIds, indent)}
                </span>
            );
        case "Ppcmd_print_break":
            console.log("ID:" + id);
            console.log("BREAK IDS: " + breakIds);
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
    breakIds: number[]
) : ReactFragment => {
    return fragmentOfPpStringWithMode(pp, PpMode.horizontal, coqCss, id, breakIds);
};

export default ppDisplay;