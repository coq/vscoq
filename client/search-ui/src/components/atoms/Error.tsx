import React, {FunctionComponent} from 'react';

import classes from './Error.module.css';
import { QueryError } from '../../types';

type ErrorProps = {
    error: QueryError; 
    className?: string[];
};

const error: FunctionComponent<ErrorProps> = (props) => {
    
    const {error, className} = props;

    const classNames = className ? className.concat([classes.ErrorMessage]) : [classes.ErrorMessage];
    
    return (
        <div className={classes.Error}>
            <span className={classes.ErrorHeader}> Error </span>
            <span className={classNames.join(' ')}> {error.message} </span>
        </div>
    );
    
};

export default error;