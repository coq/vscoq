import React, {FunctionComponent, useState} from 'react';
import { VscPass } from 'react-icons/vsc';

import GoalCollapsibleSection from './GoalCollapsibles';
import GoalTabSection from './GoalTabs';
import EmptyState from '../atoms/EmptyState';
import { GoalArray } from '../../types';


type GoalSectionProps = {
    goals: GoalArray,
    collapseGoalHandler: (id: string) => void, 
    displaySetting: string;
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals, collapseGoalHandler, displaySetting} = props;

    //This case should not happen
    if (goals === null) {
        return null;
    }

    const section = goals.length === 0 
    ? <EmptyState message="No more subgoals" icon={<VscPass/>} />
    : displaySetting === 'Tabs'
        ? <GoalTabSection goals={goals} />
        : <GoalCollapsibleSection goals={goals} collapseGoalHandler={collapseGoalHandler} />;

    return section;
};

export default goalSection;