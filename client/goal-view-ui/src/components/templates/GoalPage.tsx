import React, {FunctionComponent} from 'react'; 

import GoalTabSection from '../organisms/GoalTabs';
import GoalCollapsibleSection from '../organisms/GoalCollapsibles';

import classes from './GoalPage.module.css';

type GoalPageProps = {
    goals: {
        id: string,
        goal: string, 
        hypotheses: {
            identifiers: string[],
            type: string
        }[],
        isOpen: boolean,
        displayId: number
    }[], 
    collapseGoalHandler: (id: string) => void,
    displaySetting: string;
    isInProof: boolean;
};

const goalPage: FunctionComponent<GoalPageProps> = (props) => {

    const {goals, displaySetting, collapseGoalHandler, isInProof} = props;
    
    const goalSection = displaySetting === 'Tabs' ? 
        <GoalTabSection goals={goals} /> :
        <GoalCollapsibleSection goals={goals} collapseGoalHandler={collapseGoalHandler} />;


    const goalsOrEmpty = !isInProof
        ? "Not in proof"
        : goals.length === 0
            ? "No more subgoals"
            : goalSection;

    return (
        <div className={classes.Page}>
            {goalsOrEmpty}
        </div>
    );
};

export default goalPage;
