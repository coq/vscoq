import React, {FunctionComponent, useState} from 'react';
import {
    VSCodePanels,
    VSCodePanelTab,
    VSCodePanelView 
} from '@vscode/webview-ui-toolkit/react';
import { VscPass } from 'react-icons/vsc';

import GoalBlock from '../molecules/GoalBlock';
import EmptyState from '../atoms/EmptyState';
import { PpString } from '../../types';

type GoalSectionProps = {
    goals: {
        id: string,
        goal: PpString, 
        hypotheses: PpString[]
    }[];
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals} = props;

    const goalPanelTabs = goals.map((goal, index) => {
        const tabName = "Goal " + (index + 1);
        const tabId = "tab-" + index;
        return (
        <VSCodePanelTab id={tabId} key={tabId}>
             {tabName} 
        </VSCodePanelTab>);
    });    
    const goalPanelViews = goals.map((goal, index) => {
        
        const viewId = "view-" + index;
        return (
            <VSCodePanelView id={viewId} key={viewId}>
                <GoalBlock goal={goal}/>
            </VSCodePanelView>
        );
    });

    return (
        <VSCodePanels>
            {goalPanelTabs}
            {goalPanelViews}
        </VSCodePanels>
    );
};

export default goalSection;