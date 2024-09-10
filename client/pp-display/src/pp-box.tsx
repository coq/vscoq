import React, {FunctionComponent, useState,} from 'react';
import {Box, DisplayType, BreakInfo, HideStates } from './types';
import PpBreak from './pp-break';
import classes from './Pp.module.css';

/**
 * Computes the optimal hide state given a hide state for the current box and the hide state for the parent box .
 */
const ComputeHideState = (self : HideStates, parent : HideStates) => {
  // If "parent" state dictates "self", then follow it
  if (parent === HideStates.HIDE || parent === HideStates.EXPAND_ALL) {
    return parent;
  }
  // Otherwise, follow the self state
  return self;
}

interface PpBoxProps extends Box {
    coqCss: CSSModuleClasses,
    breaks: BreakInfo[],
    maxDepth: number,
    parentHide: HideStates,
    hovered: boolean,
    addedDepth: number,
}

const ADDED_DEPTH_FACTOR = 10;

const PpBox: FunctionComponent<PpBoxProps> = (props) => {
    
    const {mode, depth, coqCss, id, breaks, boxChildren, parentHide, hovered, maxDepth, addedDepth} = props;
    const [selfHide, setSelfHide] = useState<HideStates>(ComputeHideState(depth >= maxDepth ? HideStates.HIDE : HideStates.UNHIDE, parentHide));
    const [depthOpen, setDepthOpen] = useState<number>(addedDepth);

    const ellpisis = (
        <span className={classes.Ellipsis}>
            [...]
        </span>
    );

    const inner = selfHide === HideStates.HIDE ? ellpisis : boxChildren.map((child, i) => {
        if(child) {
            if (child.type === DisplayType.box) {
                return (
                    <PpBox
                        key={child.id + i}
                        type={child.type}
                        depth={child.depth}
                        parentHide={selfHide}
                        hovered={hovered}
                        maxDepth={maxDepth}
                        coqCss={coqCss}
                        id={child.id}
                        classList={child.classList}
                        mode={child.mode}
                        indent={child.indent}
                        breaks={breaks}
                        boxChildren={child.boxChildren}
                        addedDepth={addedDepth + depthOpen}
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
                if(e.altKey) { 
                    if (selfHide === HideStates.HIDE) {
                      setDepthOpen(depthOpen + ADDED_DEPTH_FACTOR);
                      setSelfHide(e.shiftKey ? HideStates.EXPAND_ALL : HideStates.UNHIDE);
                    } else {
                      // We must be in a visible state, so turn to hide
                      setDepthOpen(Math.max(depthOpen - ADDED_DEPTH_FACTOR, 0));
                      setSelfHide(HideStates.HIDE);
                    }
                };
            }}
        >
            {inner}
        </span>
    );
};

export default PpBox;