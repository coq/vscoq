import React, {FunctionComponent} from 'react';

import classes from './PpString.module.css';
import { PpString } from '../../types';
import PpDisplay from '../../utilities/pp';

type GoalProps = {
    goal: PpString,
    maxDepth: number,
    setHelpMessage: (message: string) => void;
};

const goal : FunctionComponent<GoalProps> = (props) => {
    
    const {goal, maxDepth, setHelpMessage} = props;

    return (
        <div 
            className={classes.Goal} 
            onMouseOver={() => {
                if(setHelpMessage !== undefined) {
                    setHelpMessage("Click on the window and keep Alt pressed in to enable term eliding/expanding.");
                }
            }}
            onMouseOut={() => {
                if(setHelpMessage !== undefined) {
                    setHelpMessage("");
                }
            }}>
            <PpDisplay 
                pp={goal}
                coqCss={classes}
                maxDepth={maxDepth}
            />
        </div>
    );
};

export default goal;

