import React, {FunctionComponent} from 'react';

import classes from './Hypothesis.module.css';

type HypothesisProps = {
    identifiers: string[], 
    type: string,
};

const hypothesis: FunctionComponent<HypothesisProps> = (props) => {
    
    const {identifiers, type} = props;

    const idString = identifiers.slice(1).reduce((pre, curr) => {
        return pre + ", " + curr;
    }, identifiers[0]);

    return (
        <div className={classes.Hypothesis}>
            <label className={classes.Identifier}>{idString}</label>
            <label className={classes.Separator}> : </label>
            <span className={classes.Type}>{type}</span>
            <br/>
        </div>
    );
};

export default hypothesis;