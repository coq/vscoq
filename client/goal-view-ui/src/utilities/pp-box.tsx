import React, {FunctionComponent, useEffect, useState, useLayoutEffect, useRef, ReactFragment, SyntheticEvent} from 'react';
import {Box, DisplayType, BreakInfo} from '../types';
import PpBreak from './pp-break';
import classes from './Pp.module.css';

interface PpBoxProps extends Box {
    coqCss: CSSModuleClasses,
    breaks: BreakInfo[],
    maxDepth: number,
    hide: boolean,
    hovered: boolean
}

const PpBox: FunctionComponent<PpBoxProps> = (props) => {
    
    const {mode, depth, coqCss, id, indent, breaks, boxChildren, hovered, maxDepth} = props;
    const [hide, setHide] = useState<boolean>(depth >= maxDepth);

    const ellpisis = (
        <span className={classes.Ellipsis}>
            [...]
        </span>
    );

    const inner = hide ? ellpisis : boxChildren.map((child, i) => {
        if(child) {
            if (child.type === DisplayType.box) {
                return (
                    <PpBox
                        key={child.id + i}
                        type={child.type}
                        depth={child.depth}
                        hide={hide}
                        hovered={hovered}
                        maxDepth={maxDepth}
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

    const classNames = hovered ? [classes.Box, classes.Hovered] : [classes.Box];

    return (
        <span 
            id={id} 
            className={classNames.join(' ')}
            onClick={(e) => {
                e.stopPropagation();
                if(e.altKey) { setHide(!hide); };
            }}
        >
            {inner}
        </span>
    );
};

export default PpBox;