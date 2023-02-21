import React, {FunctionComponent} from 'react'; 

import GoalSection from '../organisms/GoalSection';
import EmptyState from '../atoms/EmptyState';
import { GoalArrayOrNull } from '../../types';

import classes from './GoalPage.module.css';

type GoalPageProps = {
    goals: GoalArrayOrNull, 
    collapseGoalHandler: (id: string) => void,
    displaySetting: string;
};

const goalPage: FunctionComponent<GoalPageProps> = (props) => {

    const {goals, displaySetting, collapseGoalHandler} = props;
    
    const goalsOrEmpty = (goals === null) 
        ? <EmptyState message="Not in proof mode" />
        : <GoalSection goals={goals} collapseGoalHandler={collapseGoalHandler} displaySetting={displaySetting} />;
    
    return (
        <div className={classes.Page}>
            {goalsOrEmpty}
        </div>
    );
};

export default goalPage;
