import React, {FunctionComponent} from 'react';

import Hypothesis from '../atoms/Hypothesis';

import classes from './HypothesesBlock.module.css';

type HypothesesBlockProps = {
    hypotheses: {
        identifiers: string[], 
        type: string,
    }[];
};

const hypothesesBlock: FunctionComponent<HypothesesBlockProps> = (props) => {

    const {hypotheses} = props;

    const hypothesesComponents = hypotheses.map((hyp, index) => {
        return <Hypothesis key={index} identifiers={hyp.identifiers} type={hyp.type} />;
    });

    return (
        <div className={classes.Block}>
            {hypothesesComponents}
        </div>
    );
};

export default hypothesesBlock;