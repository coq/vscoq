import React, {FunctionComponent, useState, useEffect} from 'react';
import {PpMode} from '../types';

type PpBreakProps = {
    mode: PpMode,
    horizontalIndent: number, 
    indent: number,
    lineBreak: boolean 
};

const ppBreak: FunctionComponent<PpBreakProps> = (props) => {
    
    const {mode, lineBreak, indent, horizontalIndent} = props;

    switch(mode) {
        case PpMode.horizontal:
            return <span>{" ".repeat(horizontalIndent)}</span>;
        case PpMode.vertical:
            return <br/>;
        case PpMode.hvBox:
            if(lineBreak) {
                return <br/>;
            }
            return <span> </span>;
        case PpMode.hovBox:
            if(lineBreak) {
                return (
                    <>
                        <br/>
                        <span>
                            {" ".repeat(indent ? indent : 0)}
                        </span>
                    </>
                );
            }
            return <span> </span>;
    }
};

export default ppBreak;