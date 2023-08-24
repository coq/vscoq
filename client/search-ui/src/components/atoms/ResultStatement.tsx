import React, {FunctionComponent} from 'react';

import { fragmentOfPpString } from '../../utilities/pp';
import { PpString } from '../../types';

import classes from './ResultStatement.module.css';

type ResultStatementProps = {
    statement: PpString | null; 
    className?: string[];
};

const resultStatement: FunctionComponent<ResultStatementProps> = (props) => {
    
    const {statement, className} = props;

    const classNames = className ? className.concat([classes.ResultStatement]) : [classes.ResultStatement];
    
    return statement ?
        <span className={classNames.join(' ')}> {fragmentOfPpString(statement, classes)} </span>
        : null;
    
};

export default resultStatement;