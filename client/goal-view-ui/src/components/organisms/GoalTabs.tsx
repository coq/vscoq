import React, {FunctionComponent, useState} from 'react';
import {
    VSCodePanels,
    VSCodePanelTab,
    VSCodePanelView 
} from '@vscode/webview-ui-toolkit/react';

import GoalBlock from '../molecules/GoalBlock';

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

    const goalPanelTabs = goals.map(goal => {
        const tabName = "Goal " + goal.id;
        const tabId = "tab-" + goal.id;
        return (
        <VSCodePanelTab id={tabId} onClick={() => setActiveId(tabId)}>
             {tabName} 
        </VSCodePanelTab>);
    });    
    const goalPanelViews = goals.map(goal => {
        
        const tabId = "tab-" + goal.id;
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