import React, {FunctionComponent} from 'react';

import classes from './PpString.module.css';
import { Hyp } from '../../types';
import { fragmentOfPpString } from '../../utilities/pp';

type HypothesisProps = {
    content: Hyp;
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