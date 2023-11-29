import React, {FunctionComponent} from 'react';

import GoalBlock from './GoalBlock';
import Accordion from '../atoms/Accordion';
import { CollapsibleGoal } from '../../types';

type CollapsibleGoalBlockProps = {
    goal: CollapsibleGoal
    collapseHandler: (id: string) => void, 
    goalIndex: number
    goalIndicator: string
};

const collapsibleGoalBlock: FunctionComponent<CollapsibleGoalBlockProps> = (props) => {
    
    const {goal, goalIndex, goalIndicator, collapseHandler} = props;

    return (
        <Accordion title={"Goal " + goalIndex} collapsed={!goal.isOpen} collapseHandler={() => collapseHandler(goal.id)}>
            <GoalBlock goal={goal} goalIndicator={goalIndicator} />
        </Accordion>
    );

};

export default collapsibleGoalBlock;