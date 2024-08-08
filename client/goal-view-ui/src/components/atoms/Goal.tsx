import React, {FunctionComponent, MouseEvent, KeyboardEvent} from 'react';

import classes from './PpString.module.css';
import { PpDisplay, PpString } from 'pp-display';

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
            }}
        >
            <PpDisplay 
                pp={goal}
                coqCss={classes}
                maxDepth={maxDepth}
            />
        </div>
    );
};

export default goal;

