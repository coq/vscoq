import React, {FunctionComponent} from 'react';

import GoalBlock from './GoalBlock';
import Accordion from '../atoms/Accordion';
import { CollapsibleGoal } from '../../types';

type CollapsibleGoalBlockProps = {
    goal: CollapsibleGoal,
    collapseHandler: (id: string) => void, 
    goalIndex: number,
    goalIndicator: string,
    maxDepth: number,
    helpMessageHandler: (message: string) => void
};

const collapsibleGoalBlock: FunctionComponent<CollapsibleGoalBlockProps> = (props) => {
    
    const {goal, goalIndex, goalIndicator, collapseHandler, maxDepth, helpMessageHandler} = props;

    return (
        <Accordion title={"Goal " + goalIndex} collapsed={!goal.isOpen} collapseHandler={() => collapseHandler(goal.id)}>
            <GoalBlock goal={goal} goalIndicator={goalIndicator} maxDepth={maxDepth} helpMessageHandler={helpMessageHandler} displayHyps={goalIndex === 1}/>
        </Accordion>
    );

};

export default collapsibleGoalBlock;