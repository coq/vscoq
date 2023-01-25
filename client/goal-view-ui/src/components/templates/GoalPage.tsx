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
    collapseGoalHandler: (id: string) => void;
};

const goalPage: FunctionComponent<GoalPageProps> = (props) => {

    const {goals, collapseGoalHandler} = props;

    return (
        <div className={classes.Page}>
        <GoalCollapsibleSection goals={goals} collapseGoalHandler={collapseGoalHandler} />
        {/* <GoalTabSection goals={goals} /> */}
        </div>
    );
};

export default goalPage;
