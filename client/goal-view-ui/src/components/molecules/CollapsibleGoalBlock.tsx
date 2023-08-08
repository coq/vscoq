import React, {FunctionComponent} from 'react';
import {VSCodeButton} from '@vscode/webview-ui-toolkit/react';
import {VscChevronDown} from 'react-icons/vsc';

import GoalBlock from './GoalBlock';

import classes from './GoalBlock.module.css';
import { PpString } from '../../types';

type CollapsibleGoalBlockProps = {
    goal: {
        id: string, 
        goal: PpString, 
        hypotheses: PpString[]
    },
    collapseHandler: (id: string) => void, 
    isOpen: boolean,
    goalIndex: number
};

const collapsibleGoalBlock: FunctionComponent<CollapsibleGoalBlockProps> = (props) => {
    
    const {goal, goalIndex, isOpen, collapseHandler} = props;
    
    const panelClasses = [classes.Panel]; 
    if(!isOpen) {
        panelClasses.push(classes.Closed);
    }

    return (
        <div className={classes.Block}>

            {/* The header with title and button */}
            <div className={classes.Header}>
                <span className={isOpen ? classes.Demphasize : ''}>{"Goal " + goalIndex}</span>
                <VSCodeButton appearance={'icon'} ariaLabel='Collapse' onClick={() => collapseHandler(goal.id)}>
                    <VscChevronDown className={isOpen ? [classes.Rotated, classes.Demphasize].join(' ') : ''} />
                </VSCodeButton>
            </div>

            {/* The panel that collapses */}
            <div className={panelClasses.join(' ')}>
                <GoalBlock goal={goal}/>
            </div>
                

        </div>
    );

};

export default collapsibleGoalBlock;