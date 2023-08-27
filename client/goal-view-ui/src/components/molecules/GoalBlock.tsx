import React, {FunctionComponent} from 'react';
import {VSCodeButton} from '@vscode/webview-ui-toolkit/react';
import {VscChevronDown} from 'react-icons/vsc';

import HypothesesBlock from './HypothesesBlock';
import GoalComponent from '../atoms/Goal';
import Separator from '../atoms/Separator';

import classes from './GoalBlock.module.css';
import { Goal } from '../../types';

type GoalBlockProps = {
    goal: Goal
};

const goalBlock: FunctionComponent<GoalBlockProps> = (props) => {
    
    const {goal} = props;

    return (
        <div className={classes.Block}>
            <HypothesesBlock hypotheses={goal.hypotheses}/>
            <GoalComponent goal={goal.goal}/>
        </div>
    );
};

export default goalBlock;