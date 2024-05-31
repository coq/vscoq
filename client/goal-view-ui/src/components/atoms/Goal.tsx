import React, {FunctionComponent} from 'react';

import classes from './PpString.module.css';
import { PpString } from '../../types';
import PpDisplay from '../../utilities/pp';

type GoalProps = {
    goal: PpString, 
};

const goal : FunctionComponent<GoalProps> = (props) => {
    
    const {goal} = props;

    return (
        <div className={classes.Goal}>
            <PpDisplay 
                pp={goal}
                coqCss={classes}
            />
        </div>
    );
};

export default goal;

