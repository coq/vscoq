import React, {FunctionComponent} from 'react';
import {PpMode} from './types';

type PpBreakProps = {
    id: string,
    offset: number,
    mode: PpMode,
    horizontalIndent: number,
    lineBreak: boolean,
};

const ppBreak: FunctionComponent<PpBreakProps> = (props) => {
    
    const {mode, lineBreak, horizontalIndent, id, offset} = props;
    const style = {
        marginLeft: offset
    };

    switch(mode) {
        case PpMode.horizontal:
            return <span id={id}>{" ".repeat(horizontalIndent)}</span>;
        //in the case of PpMode.vertical we always detect the line break in the scan part of the algo
        //this allows to set the correct offset
        case PpMode.vertical:
        case PpMode.hvBox:
        case PpMode.hovBox:
            if(lineBreak) {
                return (
                    <span id={id}>
                        <br/>
                        <span style={style}>
                        </span>
                    </span>
                );
            }
            return <span id={id}> </span>;
    }
};

export default ppBreak;