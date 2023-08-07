import React, {FunctionComponent} from 'react';

import Hypothesis from '../atoms/Hypothesis';

import classes from './HypothesesBlock.module.css';
import { PpString } from '../../types';

type HypothesesBlockProps = {
    hypotheses: {
        identifiers: string[], 
        type: PpString,
    }[];
};

const hypothesesBlock: FunctionComponent<HypothesesBlockProps> = (props) => {

    const {hypotheses} = props;

    const hypothesesComponents = hypotheses.map((hyp, index) => {
        return <Hypothesis key={index} identifiers={hyp.identifiers} type={hyp.type} />;
    });

    return (
        <ul className={classes.Block}>
            {hypothesesComponents}
        </ul>
    );
};

export default hypothesesBlock;