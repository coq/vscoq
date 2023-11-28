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
    goalIndicator?: string
};

const goalBlock: FunctionComponent<GoalBlockProps> = (props) => {
    
    const {goal, goalIndicator} = props;
    const indicator = goalIndicator ? <span className={classes.GoalIndex} >({goalIndicator})</span> : null;

    return (
        <div className={classes.Block}>
            <HypothesesBlock hypotheses={goal.hypotheses}/>
            <div className={classes.SeparatorZone}> {indicator} <Separator /> </div>
            <GoalComponent goal={goal.goal}/>
        </div>
    );
};

export default goalBlock;