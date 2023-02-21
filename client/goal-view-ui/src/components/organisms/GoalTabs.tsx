import React, {FunctionComponent, useState} from 'react';
import {
    VSCodePanels,
    VSCodePanelTab,
    VSCodePanelView 
} from '@vscode/webview-ui-toolkit/react';
import { VscPass } from 'react-icons/vsc';

import GoalBlock from '../molecules/GoalBlock';
import EmptyState from '../atoms/EmptyState';

type GoalSectionProps = {
    goals: {
        id: string,
        goal: string, 
        hypotheses: {
            identifiers: string[],
            type: string
        }[]
    }[];
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals} = props;

    const [activeId, setActiveId] = useState("tab-0");

    const goalPanelTabs = goals.map((goal, index) => {
        const tabName = "Goal " + (index + 1);
        const tabId = "tab-" + index;
        return (
        <VSCodePanelTab id={tabId} onClick={() => setActiveId(tabId)}>
             {tabName} 
        </VSCodePanelTab>);
    });    
    const goalPanelViews = goals.map((goal, index) => {
        
        const tabId = "tab-" + index;
        return (
            <VSCodePanelView id={tabId}>
                <GoalBlock goal={goal}/>
            </VSCodePanelView>
        );
    });

    return (
        <VSCodePanels activeid={activeId}>
            {goalPanelTabs}
            {goalPanelViews}
        </VSCodePanels>
    );
};

export default goalSection;