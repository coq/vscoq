import React, {FunctionComponent} from 'react';
import {PpMode} from '../types';

type PpBreakProps = {
    id: number,
    offset: number,
    mode: PpMode,
    horizontalIndent: number, 
    indent: number,
    lineBreak: boolean,
};

const ppBreak: FunctionComponent<PpBreakProps> = (props) => {
    
    const {mode, lineBreak, indent, horizontalIndent, id, offset} = props;
    const style = {
        marginLeft: offset
    };
    
    const breakId = 'break-'+id;
    switch(mode) {
        case PpMode.horizontal:
            return <span id={breakId}>{" ".repeat(horizontalIndent)}</span>;
        case PpMode.vertical:
            return (
                <span id={breakId}>
                    <br/>
                    <span style={style}>
                        {" ".repeat(indent ? indent : 0)}
                    </span>
                </span>
            );
        case PpMode.hvBox:
            if(lineBreak) {
                <span id={breakId}>
                    <br/>
                    <span style={style}>
                        {" ".repeat(indent ? indent : 0)}
                    </span>
                </span>;
            }
            return <span id={breakId}> </span>;
        case PpMode.hovBox:
            if(lineBreak) {
                return (
                    <span id={breakId}>
                        <br/>
                        <span style={style}>
                            {" ".repeat(indent ? indent : 0)}
                        </span>
                    </span>
                );
            }
            return <span id={breakId}> </span>;
    }
};

export default ppBreak;