import React, {FunctionComponent} from 'react';

import classes from './ResultStatement.module.css';

type ResultStatementProps = {
    statement: string; 
    className?: string[];
};

const resultStatement: FunctionComponent<ResultStatementProps> = (props) => {
    
    const {statement, className} = props;

    const classNames = className ? className.concat([classes.ResultStatement]) : [classes.ResultStatement];
    
    return <span className={classNames.join(' ')}> {statement} </span>;
    
};

export default resultStatement;