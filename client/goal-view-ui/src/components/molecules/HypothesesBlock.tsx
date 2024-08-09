import React, {FunctionComponent} from 'react';

import { PpString } from 'pp-display';

import Hypothesis from '../atoms/Hypothesis';

import classes from './HypothesesBlock.module.css';

type HypothesesBlockProps = {
    hypotheses: PpString[];
    maxDepth: number
};

const hypothesesBlock: FunctionComponent<HypothesesBlockProps> = (props) => {

    const {hypotheses, maxDepth} = props;

    const hypothesesComponents = hypotheses.map((hyp, index) => {
        return <Hypothesis key={index} content={hyp} maxDepth={maxDepth}/>;
    });

    return (
        <ul className={classes.Block}>
            {hypothesesComponents}
        </ul>
    );
};

export default hypothesesBlock;