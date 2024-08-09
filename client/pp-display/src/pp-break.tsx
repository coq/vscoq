import React, {FunctionComponent} from 'react';
import {PpMode} from './types';

type PpBreakProps = {
    id: string,
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

    switch(mode) {
        case PpMode.horizontal:
            return <span id={id}>{" ".repeat(horizontalIndent)}</span>;
        case PpMode.vertical:
            return (
                <span id={id}>
                    <br/>
                    <span style={style}>
                        {" ".repeat(indent ? indent : 0)}
                    </span>
                </span>
            );
        case PpMode.hvBox:
            if(lineBreak) {
                <span id={id}>
                    <br/>
                    <span style={style}>
                        {" ".repeat(indent ? indent : 0)}
                    </span>
                </span>;
            }
            return <span id={id}> </span>;
        case PpMode.hovBox:
            if(lineBreak) {
                return (
                    <span id={id}>
                        <br/>
                        <span style={style}>
                            {" ".repeat(indent ? indent : 0)}
                        </span>
                    </span>
                );
            }
            return <span id={id}> </span>;
    }
};

export default ppBreak;