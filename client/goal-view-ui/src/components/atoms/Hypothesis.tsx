import React, {FunctionComponent} from 'react';

import classes from './PpString.module.css';
import { PpDisplay, PpString } from 'pp-display';

type HypothesisProps = {
    content: PpString;
    maxDepth: number;
};

const hypothesis: FunctionComponent<HypothesisProps> = (props) => {
    
    const {content, maxDepth} = props;

    return (
        <div className={classes.Hypothesis}>
            <PpDisplay 
                pp={content}
                coqCss={classes}
                maxDepth={maxDepth}
            />
        </div>
    );
};

export default hypothesis;