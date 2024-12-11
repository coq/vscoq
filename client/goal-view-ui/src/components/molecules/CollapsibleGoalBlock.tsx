import React, {FunctionComponent} from 'react';

import { VscEye, VscEyeClosed } from 'react-icons/vsc';

import GoalBlock from './GoalBlock';
import Accordion from '../atoms/Accordion';
import { CollapsibleGoal } from '../../types';

type CollapsibleGoalBlockProps = {
    goal: CollapsibleGoal,
    collapseHandler: (id: string) => void,
    toggleContextHandler: (id:string) => void,
    goalIndex: number,
    goalIndicator: string,
    maxDepth: number,
    helpMessageHandler: (message: string) => void
};

const collapsibleGoalBlock: FunctionComponent<CollapsibleGoalBlockProps> = (props) => {
    
    const {goal, goalIndex, goalIndicator, collapseHandler, toggleContextHandler, maxDepth, helpMessageHandler} = props;

    const secondaryActionIcon = goal.isContextHidden ? <VscEye /> : <VscEyeClosed />;
    const secondaryActionHandler = toggleContextHandler !== undefined ? () => toggleContextHandler(goal.id) : undefined;

    return (
        <Accordion title={"Goal " + goalIndex} collapsed={!goal.isOpen} 
            collapseHandler={() => collapseHandler(goal.id)}
            seconaryActionHandler={secondaryActionHandler}
            seconaryActionIcon={secondaryActionIcon}
        >
            <GoalBlock goal={goal} goalIndicator={goalIndicator} maxDepth={maxDepth} helpMessageHandler={helpMessageHandler} displayHyps={!goal.isContextHidden}/>
        </Accordion>
    );

};

export default collapsibleGoalBlock;