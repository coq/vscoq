import React, {FunctionComponent, useState} from 'react';

import CollapsibleGoalBlock from '../molecules/CollapsibleGoalBlock';

type GoalSectionProps = {
    goals: {
        id: string,
        goal: string, 
        hypotheses: {
            identifiers: string[],
            type: string
        }[],
        isOpen: boolean
    }[],
    collapseGoalHandler: (id: string) => void, 
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals, collapseGoalHandler} = props;

    const goalCollapsibles = goals.map((goal, index) => {
        
        return (
            <CollapsibleGoalBlock goal={goal} goalIndex={index + 1} isOpen={goal.isOpen} collapseHandler={collapseGoalHandler}/>
        );
    });

    return (
        <div>
            {goalCollapsibles}
        </div>
    );
};

export default goalSection;