import React, {FunctionComponent} from 'react';

import ResultStatement from '../atoms/ResultStatement';

import { QueryResultBase } from '../../types';

//TODO: At some point we will restyle this
import classes from './SearchResult.module.css';

//At the moment Coq only returns a unique string as the about result
type QueryResultProps = {
    result: QueryResultBase; 
};

const aboutResult: FunctionComponent<QueryResultProps> = (props) => {
    
    const {result} = props;

    return (
        <div className={classes.ResultBlock}>

            <ResultStatement statement={result.statement}/>

        </div>
    );
};

export default aboutResult;