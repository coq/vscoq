import React, {FunctionComponent, useEffect, useState, useLayoutEffect, useRef} from 'react';
import {PpMode, PpString} from '../types';
import { fragmentOfPpStringWithMode } from './pp';
import classes from './Pp.module.css';

type BreakInfo = {
    id: string,
    offset: number
};

type PpBoxProps = {
    pp: PpString,
    mode: PpMode,
    recordWidth: (id: string, w: number) => void,
    coqCss:CSSModuleClasses,
    indent: number,
    id: number,
    breaks: BreakInfo[]
};

const ppBox: FunctionComponent<PpBoxProps> = (props) => {
    
    const {pp, mode, recordWidth, coqCss, id, indent, breaks} = props;
    const boxElement = useRef<HTMLSpanElement>(null);

    useEffect(() => {
        if(boxElement.current) {
            const boxRect = boxElement.current.getBoundingClientRect();
            recordWidth("box-"+id, boxRect.width);
            boxElement.current.closest(classes.Box);

        }
    }, [breaks]);

    const boxId = "box-"+id;
    return (
        <span ref={boxElement} id={boxId} className={classes.Box}>
            {fragmentOfPpStringWithMode(pp, mode, coqCss, id + 1, breaks, indent, recordWidth)}
        </span>
    );
};

export default ppBox;