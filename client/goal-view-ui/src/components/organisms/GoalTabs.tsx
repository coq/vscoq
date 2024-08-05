import React, {FunctionComponent, useRef, useLayoutEffect} from 'react';
import {
    VSCodePanels,
    VSCodePanelTab,
    VSCodePanelView 
} from '@vscode/webview-ui-toolkit/react';

import GoalBlock from '../molecules/GoalBlock';
import { Goal } from '../../types';

import classes from './GoalTabs.module.css';

type GoalSectionProps = {
    goals: Goal[];
    maxDepth: number;
    helpMessageHandler: (message: string) => void;
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals, maxDepth, helpMessageHandler} = props;
    const goalRefs = useRef<Array<HTMLDivElement | null>>([]);
    useLayoutEffect(() => {
        goalRefs.current = goalRefs.current.slice(0, goals.length);
        setTimeout(() => scrollToBottomOfGoal(0), 200);
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
                <GoalBlock goal={goal} goalIndicator={index + 1 + " / " + goals.length} maxDepth={maxDepth} helpMessageHandler={helpMessageHandler}/>
                <div ref={el => goalRefs.current[index] = el}/>
            </VSCodePanelView>
        );
    });

    return (
        <VSCodePanels className={classes.View}>
            {goalPanelTabs}
            {goalPanelViews}
        </VSCodePanels>
    );
};

export default goalSection;