import React, {FunctionComponent} from 'react';

import classes from './PpString.module.css';
import { Hyp } from '../../types';
import PpDisplay from '../../utilities/pp';

type HypothesisProps = {
    content: Hyp;
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