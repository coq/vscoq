import React, {FunctionComponent} from 'react';

import classes from './PpString.module.css';
import { MessageSeverity, PpString } from '../../types';
import { fragmentOfPpString } from '../../utilities/pp';

type MessageProps = {
    message: PpString,
    severity: MessageSeverity
};

const message : FunctionComponent<MessageProps> = (props) => {
    
    const {message, severity} = props;

    const classNames = [classes.Message]; 

    switch(severity) {
        case MessageSeverity.error:
            classNames.push(classes.Error);
            break;

        case MessageSeverity.information: 
            classNames.push(classes.Info);
            break;

        case MessageSeverity.hint: 
            classNames.push(classes.Hint);
            break;

        case MessageSeverity.warning: 
            classNames.push(classes.Warning);
            break;
    }

    return (
        <span className={classNames.join(' ')}>
            {fragmentOfPpString(message, classes)}
        </span>
    );
};

export default message;

