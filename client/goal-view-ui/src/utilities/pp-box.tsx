import React, {FunctionComponent, useEffect, useState, useLayoutEffect, useRef, ReactFragment} from 'react';
import {Box, DisplayType, BreakInfo} from '../types';
import PpBreak from './pp-break';
import classes from './Pp.module.css';

interface PpBoxProps extends Box {
    coqCss: CSSModuleClasses,
    breaks: BreakInfo[]
}

const PpBox: FunctionComponent<PpBoxProps> = (props) => {
    
    const {mode, coqCss, id, indent, breaks, boxChildren} = props;

    const inner = boxChildren.map((child, i) => {
        if(child) {
            if (child.type === DisplayType.box) {
                return (
                    <PpBox
                        key={child.id + i}
                        type={child.type}
                        coqCss={coqCss}
                        id={child.id}
                        classList={child.classList}
                        mode={child.mode}
                        indent={child.indent}
                        breaks={breaks}
                        boxChildren={child.boxChildren}
                    />
                );
            } else if (child.type === DisplayType.break) {
                const lineBreak = (breaks.find(br => br.id === child.id));
                return (
                    <PpBreak
                        key={child.id + i}
                        id={child.id}
                        offset={lineBreak ? lineBreak.offset : 0}
                        mode={mode}
                        horizontalIndent={child.horizontalIndent}
                        indent={indent}
                        lineBreak={lineBreak !== undefined}
                    />
                );
            } else {
                return (
                    <span key={"term" + i} className={child.classList.join(' ')}>
                        {child.content}
                    </span>
                );
            }
        }
    });

    return (
        <span id={id} className={classes.Box}>
            {inner}
        </span>
    );
};

export default PpBox;