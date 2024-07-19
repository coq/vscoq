import React, {FunctionComponent} from 'react';

import classes from './PpString.module.css';
import { PpString } from '../../types';
import PpDisplay from '../../utilities/pp';

type GoalProps = {
    goal: PpString,
    maxDepth: number
};

const goal : FunctionComponent<GoalProps> = (props) => {
    
    const {goal, maxDepth} = props;

    return (
        <div className={classes.Goal}>
            <PpDisplay 
                pp={goal}
                coqCss={classes}
                maxDepth={maxDepth}
            />
        </div>
    );
};

export default goal;

