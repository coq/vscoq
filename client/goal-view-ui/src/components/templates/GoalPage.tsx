import React, {FunctionComponent} from 'react'; 

import GoalSection from '../organisms/GoalSection';
import EmptyState from '../atoms/EmptyState';
import { VscDebugPause } from 'react-icons/vsc';


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
    
    const goalsOrEmpty = !isInProof 
        ? <EmptyState message="Not in proof mode" />
        : <GoalSection goals={goals} collapseGoalHandler={collapseGoalHandler} displaySetting={displaySetting} />;
    
    return (
        <div className={classes.Page}>
            {goalsOrEmpty}
        </div>
    );
};

export default goalPage;
