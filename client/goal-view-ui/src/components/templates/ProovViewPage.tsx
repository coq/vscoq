import React, {FunctionComponent} from 'react'; 

import { 
    VSCodeBadge, 
    VSCodePanels, 
    VSCodePanelTab, 
    VSCodePanelView 
} from '@vscode/webview-ui-toolkit/react';

import GoalSection from '../organisms/GoalSection';
import EmptyState from '../atoms/EmptyState';
import { ProofView, ProofViewKey } from '../../types';

import classes from './GoalPage.module.css';

type ProofViewPageProps = {
    proofView: ProofView, 
    collapseGoalHandler: (id: string, key: ProofViewKey) => void,
    displaySetting: string;
};

const proofViewPage: FunctionComponent<ProofViewPageProps> = (props) => {

    const {proofView, displaySetting, collapseGoalHandler} = props;

    const renderProofView = () => {
        const goalBadge = <VSCodeBadge>{proofView!.goals.length}</VSCodeBadge>;
        const shelvedBadge = <VSCodeBadge>{proofView!.shelvedGoals.length}</VSCodeBadge>;
        const givenUpBadge = <VSCodeBadge>{proofView!.givenUpGoals.length}</VSCodeBadge>;

        const tabs = [
            <VSCodePanelTab>Main {goalBadge}</VSCodePanelTab>,
            <VSCodePanelTab>Shelved {shelvedBadge}</VSCodePanelTab>,
            <VSCodePanelTab>Given up {givenUpBadge}</VSCodePanelTab>
        ];

        const views = [
            <VSCodePanelView> <GoalSection goals={proofView!.goals} collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewKey.goals)} displaySetting={displaySetting}/> </VSCodePanelView>,
            <VSCodePanelView> <GoalSection goals={proofView!.shelvedGoals} collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewKey.shelved)} displaySetting={displaySetting}/> </VSCodePanelView>,
            <VSCodePanelView> <GoalSection goals={proofView!.givenUpGoals} collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewKey.givenUp)} displaySetting={displaySetting}/> </VSCodePanelView>
        ];

        return (
            <VSCodePanels>
                {tabs}
                {views}
            </VSCodePanels>
        );
    };
    
    const display = (proofView === null) 
        ? <EmptyState message="Not in proof mode" />
        : renderProofView(); 
    
    return (
        <div className={classes.Page}>
            {display}
        </div>
    );
};

export default proofViewPage;
