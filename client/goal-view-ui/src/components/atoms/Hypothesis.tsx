import React, {FunctionComponent} from 'react';

import classes from './Hypothesis.module.css';
import { PpString } from '../../types';
import { fragmentOfPpString } from '../../utilities/pp';

type HypothesisProps = {
    content: PpString,
};

const hypothesis: FunctionComponent<HypothesisProps> = (props) => {
    
    const {content} = props;

    return (
        <div className={classes.Hypothesis}>
            <span className={classes.Content}>{fragmentOfPpString(content, classes)}</span>
            <br/>
        </div>
    );
};

export default hypothesis;