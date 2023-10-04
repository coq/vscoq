import React, {FunctionComponent, ReactNode, useState} from 'react';
import { VscPass } from 'react-icons/vsc';

import GoalCollapsibleSection from './GoalCollapsibles';
import GoalTabSection from './GoalTabs';
import EmptyState from '../atoms/EmptyState';
import { CollapsibleGoal } from '../../types';


type GoalSectionProps = {
    goals: CollapsibleGoal[],
    collapseGoalHandler: (id: string) => void, 
    displaySetting: string;
    emptyMessage: string;
    emptyIcon?: JSX.Element
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals, collapseGoalHandler, displaySetting, emptyMessage, emptyIcon} = props;

    //This case should not happen
    if (goals === null) {
        return null;
    }

    const section = goals.length === 0 
    ? <EmptyState message={emptyMessage} icon={emptyIcon} />
    : displaySetting === 'Tabs'
        ? <GoalTabSection goals={goals} />
        : <GoalCollapsibleSection goals={goals} collapseGoalHandler={collapseGoalHandler} />;

    return section;
};

export default goalSection;