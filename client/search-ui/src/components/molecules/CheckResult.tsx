import React, {FunctionComponent} from 'react';

import ResultStatement from '../atoms/ResultStatement';

//TODO: At some point we will restyle this
import classes from './SearchResult.module.css';

//At the moment Coq only returns a unique string as the about result
type CheckResultProps = {
    statement: string; 
};

const checkResult: FunctionComponent<CheckResultProps> = (props) => {
    
    const {statement} = props;

    return (
        <div className={classes.ResultBlock}>

            <ResultStatement statement={statement}/>

        </div>
    );
};

export default checkResult;