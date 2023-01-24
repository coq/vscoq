import React, {FunctionComponent} from 'react';

import classes from './Goal.module.css';

type GoalProps = {
    goalId: string, 
    goal: string, 
};

const goal : FunctionComponent<GoalProps> = (props) => {
    
    const {goalId, goal} = props;

    return (
        <div className={classes.Goal}>
            {goal}
        </div>
    );
};

export default goal;

