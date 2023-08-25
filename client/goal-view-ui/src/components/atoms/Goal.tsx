import React, {FunctionComponent} from 'react';

import classes from './PpString.module.css';
import { PpString } from '../../types';
import { fragmentOfPpString } from '../../utilities/pp';

type GoalProps = {
    goal: PpString, 
};

const goal : FunctionComponent<GoalProps> = (props) => {
    
    const {goal} = props;

    return (
        <div className={classes.Goal}>
            {fragmentOfPpString(goal, classes)}
        </div>
    );
};

export default goal;

