import React, {FunctionComponent, useRef, useEffect} from 'react';
import {
    VSCodePanels,
    VSCodePanelTab,
    VSCodePanelView 
} from '@vscode/webview-ui-toolkit/react';

import GoalBlock from '../molecules/GoalBlock';
import { Goal } from '../../types';

type GoalSectionProps = {
    goals: Goal[];
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals} = props;
    const goalRefs = useRef<Array<HTMLDivElement | null>>([]);
    useEffect(() => {
        goalRefs.current = goalRefs.current.slice(0, goals.length);
        scrollToBottomOfGoal(0);
    }, [goals]);

    const scrollToBottomOfGoal = (i : number) => {
        if(goalRefs.current) {
            if(goalRefs.current[i]) {
                goalRefs.current[i]!.scrollIntoView({
                    behavior: "smooth",
                    block: "end",
                    inline: "nearest"
                });
            }
        }
    };

    const goalPanelTabs = goals.map((goal, index) => {
        const tabName = "Goal " + (index + 1);
        const tabId = "tab-" + index;
        return (
            <VSCodePanelTab id={tabId} key={tabId} onClick={() => scrollToBottomOfGoal(index)}>
                {tabName}
            </VSCodePanelTab>);
        });

    const goalPanelViews = goals.map((goal, index) => {
        
        const viewId = "view-" + index;
        return (
            <VSCodePanelView id={viewId} key={viewId}>
                <GoalBlock goal={goal}/>
                <div ref={el => goalRefs.current[index] = el}/>
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