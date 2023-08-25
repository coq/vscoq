import React, {FunctionComponent} from 'react';
import {VSCodeButton} from '@vscode/webview-ui-toolkit/react';
import {VscChevronDown} from 'react-icons/vsc';

import GoalBlock from './GoalBlock';
import Accordion from '../atoms/Accordion';

import classes from './GoalBlock.module.css';
import { CollapsibleGoal } from '../../types';

type CollapsibleGoalBlockProps = {
    goal: CollapsibleGoal
    collapseHandler: (id: string) => void, 
    goalIndex: number
};

const collapsibleGoalBlock: FunctionComponent<CollapsibleGoalBlockProps> = (props) => {
    
    const {goal, goalIndex, collapseHandler} = props;

    return (
        <Accordion title={"Goal " + goalIndex} collapsed={!goal.isOpen} collapseHandler={() => collapseHandler(goal.id)}>
            <GoalBlock goal={goal}/>
        </Accordion>
    );

};

export default collapsibleGoalBlock;

// <div className={classes.Block}>

        //     {/* The header with title and button */}
        //     <div className={classes.Header}>
        //         <span className={goal.isOpen ? classes.Demphasize : ''}>{"Goal " + goalIndex}</span>
        //         <VSCodeButton appearance={'icon'} ariaLabel='Collapse' onClick={() => collapseHandler(goal.id)}>
        //             <VscChevronDown className={goal.isOpen ? [classes.Rotated, classes.Demphasize].join(' ') : ''} />
        //         </VSCodeButton>
        //     </div>

        //     {/* The panel that collapses */}
        //     <div className={panelClasses.join(' ')}>
        //         <GoalBlock goal={goal}/>
        //     </div>
                

        // </div>