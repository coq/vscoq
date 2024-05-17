import React, {FunctionComponent, useEffect, useRef} from 'react';
import {PpMode, PpString} from '../types';
import { fragmentOfPpStringWithMode } from './pp';

type PpBoxProps = {
    pp: PpString,
    mode: PpMode,
    recordWidth: (id: number, w: number) => void,
    coqCss:CSSModuleClasses,
    indent: number,
    id: number,
    breaks: number[]
};

const ppBox: FunctionComponent<PpBoxProps> = (props) => {
    
    const {pp, mode, recordWidth, coqCss, id, indent, breaks} = props;
    const boxElement = useRef<HTMLSpanElement>(null);

    useEffect(() => {
        if(boxElement.current) {
            const boxRect = boxElement.current.getBoundingClientRect();
            recordWidth(id, boxRect.width);
        }
    }, [breaks]);

    return (
        <span ref={boxElement}>
            {fragmentOfPpStringWithMode(pp, mode, coqCss, id + 1, breaks, indent, recordWidth)}
        </span>
    );
};

export default ppBox;