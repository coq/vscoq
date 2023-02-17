import React, {FunctionComponent, useState} from 'react';
import { VscPass } from 'react-icons/vsc';

import GoalCollapsibleSection from './GoalCollapsibles';
import GoalTabSection from './GoalTabs';
import EmptyState from '../atoms/EmptyState';


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
    displaySetting: string;
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals, collapseGoalHandler, displaySetting} = props;

    const section = goals.length === 0 
    ? <EmptyState message="No more subgoals" icon={<VscPass/>} />
    : displaySetting === 'Tabs'
        ? <GoalTabSection goals={goals} />
        : <GoalCollapsibleSection goals={goals} collapseGoalHandler={collapseGoalHandler} />;

    return section;
};

export default goalSection;