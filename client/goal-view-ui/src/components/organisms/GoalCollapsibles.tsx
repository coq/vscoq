import React, {FunctionComponent, useState} from 'react';

import CollapsibleGoalBlock from '../molecules/CollapsibleGoalBlock';
import { CollapsibleGoal } from '../../types';

import classes from './GoalCollapsibles.module.css';

type GoalSectionProps = {
    goals: CollapsibleGoal[],
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
        <div className={classes.Collapsibles}>
            {goalCollapsibles}
        </div>
    );
};

export default goalSection;