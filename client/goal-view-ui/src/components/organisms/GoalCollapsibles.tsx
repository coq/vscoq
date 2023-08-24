import React, {FunctionComponent, useState} from 'react';

import CollapsibleGoalBlock from '../molecules/CollapsibleGoalBlock';
import { DisplayedGoal } from '../../types';

type GoalSectionProps = {
    goals: DisplayedGoal[],
    collapseGoalHandler: (id: string) => void, 
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals, collapseGoalHandler} = props;
    
    
    const goalCollapsibles = goals.map((goal, index) => {
        
        return (
            <CollapsibleGoalBlock goal={goal} goalIndex={index + 1} collapseHandler={collapseGoalHandler}/>
        );
    });

    return (
        <div>
            {goalCollapsibles}
        </div>
    );
};

export default goalSection;