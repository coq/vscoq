import React, {FunctionComponent} from 'react'; 

import { 
    VSCodeBadge, 
    VSCodePanels, 
    VSCodePanelTab, 
    VSCodePanelView 
} from '@vscode/webview-ui-toolkit/react';

import GoalSection from '../organisms/GoalSection';
import EmptyState from '../atoms/EmptyState';
import { ProofViewGoals, ProofViewGoalsKey, ProofViewMessage } from '../../types';

import classes from './GoalPage.module.css';

type ProofViewPageProps = {
    goals: ProofViewGoals, 
    messages: ProofViewMessage[],
    collapseGoalHandler: (id: string, key: ProofViewGoalsKey) => void,
    displaySetting: string;
};

const proofViewPage: FunctionComponent<ProofViewPageProps> = (props) => {

    const {goals, messages, displaySetting, collapseGoalHandler} = props;

    const renderGoals = () => {
        const goalBadge = <VSCodeBadge>{goals!.main.length}</VSCodeBadge>;
        const shelvedBadge = <VSCodeBadge>{goals!.shelved.length}</VSCodeBadge>;
        const givenUpBadge = <VSCodeBadge>{goals!.givenUp.length}</VSCodeBadge>;

        const tabs = [
            <VSCodePanelTab>Main {goalBadge}</VSCodePanelTab>,
            <VSCodePanelTab>Shelved {shelvedBadge}</VSCodePanelTab>,
            <VSCodePanelTab>Given up {givenUpBadge}</VSCodePanelTab>
        ];

        const views = [
            <VSCodePanelView> <GoalSection goals={goals!.main} collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewGoalsKey.main)} displaySetting={displaySetting}/> </VSCodePanelView>,
            <VSCodePanelView> <GoalSection goals={goals!.shelved} collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewGoalsKey.shelved)} displaySetting={displaySetting}/> </VSCodePanelView>,
            <VSCodePanelView> <GoalSection goals={goals!.givenUp} collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewGoalsKey.givenUp)} displaySetting={displaySetting}/> </VSCodePanelView>
        ];

        return (
            <VSCodePanels>
                {tabs}
                {views}
            </VSCodePanels>
        );
    };
    
    const collapsibleGoalsDisplay = (goals === null) 
        ? <EmptyState message="Not in proof mode" />
        : renderGoals(); 
    
    return (
        <div className={classes.Page}>
            {collapsibleGoalsDisplay}
        </div>
    );
};

export default proofViewPage;
