import React, {FunctionComponent} from 'react';

import HypothesesBlock from './HypothesesBlock';
import Goal from '../atoms/Goal';
import Separator from '../atoms/Separator';

import classes from './GoalBlock.module.css';

type GoalBlockProps = {
    goal: {
        id: string, 
        goal: string, 
        hypotheses: {
            identifiers: string[],
            type: string, 
        }[]
    }
};

const goalBlock: FunctionComponent<GoalBlockProps> = (props) => {
    
    const {goal} = props;

    console.log('goal view', goal);

    return (
        <div className={classes.Block}>
            <HypothesesBlock hypotheses={goal.hypotheses}/>
            <Separator />
            <Goal goalId={goal.id} goal={goal.goal}/>
        </div>
    );
};

export default goalBlock;