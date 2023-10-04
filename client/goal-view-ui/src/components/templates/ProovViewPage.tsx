import React, {FunctionComponent} from 'react'; 

import { 
    VSCodeBadge, 
    VSCodePanels, 
    VSCodePanelTab, 
    VSCodePanelView 
} from '@vscode/webview-ui-toolkit/react';

import GoalSection from '../organisms/GoalSection';
import EmptyState from '../atoms/EmptyState';
import Accordion from '../atoms/Accordion';
import Message from '../atoms/Message';
import { ProofViewGoals, ProofViewGoalsKey, ProofViewMessage } from '../../types';

import classes from './GoalPage.module.css';
import { VscPass, VscWarning } from 'react-icons/vsc';

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
            <VSCodePanelView> 
                <GoalSection 
                    key={"goals"}
                    goals={goals!.main} 
                    collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewGoalsKey.main)} 
                    displaySetting={displaySetting}
                    emptyMessage={
                        goals!.shelved.length ? "There are shelved goals. Try using unshelved" :
                        goals!.givenUp.length ? "There are some goals you gave up. Go back and solve them, or use `Admitted.`" :
                        "There are no more subgoals"
                    }
                    emptyIcon={
                        goals!.shelved.length === 0 && goals!.givenUp.length === 0 ? <VscPass /> : <VscWarning />
                    }
                /> 
            </VSCodePanelView>,
            <VSCodePanelView> 
                <GoalSection 
                    key="shelved"
                    goals={goals!.shelved} 
                    collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewGoalsKey.shelved)} 
                    displaySetting={displaySetting}
                    emptyMessage='There are no shelved goals'
                /> 
            </VSCodePanelView>,
            <VSCodePanelView> 
                <GoalSection
                    key="givenup"
                    goals={goals!.givenUp} 
                    collapseGoalHandler={(id) => collapseGoalHandler(id, ProofViewGoalsKey.givenUp)} 
                    displaySetting={displaySetting}
                    emptyMessage='There are no given up goals'
                /> 
            </VSCodePanelView>
        ];

        return (
            <VSCodePanels>
                {tabs}
                {views}
            </VSCodePanels>
        );
    };

    const displayMessages = messages.map(m => {
        return (
            <Message message={m[1]} severity={m[0]}/>
        );
    });
    
    const collapsibleGoalsDisplay = (goals === null) 
        ? <EmptyState message="Not in proof mode" />
        : renderGoals(); 
    
    return (
        <div className={classes.Page}>
            <Accordion title={'Proof'} collapsed={false}>
                {collapsibleGoalsDisplay}
            </Accordion>
            <Accordion title='Messages' collapsed={false}>
                <div className={classes.Panel}>
                    {displayMessages}
                </div>
            </Accordion>
        </div>
    );
};

export default proofViewPage;
