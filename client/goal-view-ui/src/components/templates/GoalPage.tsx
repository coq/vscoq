import React, {FunctionComponent} from 'react'; 

import GoalSection from '../organisms/GoalSection';

import classes from './GoalPage.module.css';

type GoalPageProps = {
    goals: {
        id: string,
        goal: string, 
        hypotheses: {
            identifiers: string[],
            type: string
        }[]
    }[];
};

const goalPage: FunctionComponent<GoalPageProps> = (props) => {

    const {goals} = props;

    return (
        <div className={classes.Page}>
            <GoalSection goals={goals} />
        </div>
    );
};

export default goalPage;
