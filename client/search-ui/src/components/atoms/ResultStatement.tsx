import React, {FunctionComponent} from 'react';

import classes from './ResultStatement.module.css';

type ResultStatementProps = {
    statement: string; 
};

const resultStatement: FunctionComponent<ResultStatementProps> = (props) => {
    
    const {statement} = props;
    
    return <span className={classes.ResultStatement}> {statement} </span>;
    
};

export default resultStatement;