import React, {FunctionComponent, useEffect, useRef} from 'react';

import CollapsibleGoalBlock from '../molecules/CollapsibleGoalBlock';
import { CollapsibleGoal } from '../../types';

import classes from './GoalCollapsibles.module.css';

type GoalSectionProps = {
    goals: CollapsibleGoal[],
    collapseGoalHandler: (id: string) => void,
    toggleContextHandler: (id: string) => void,
    maxDepth: number,
    helpMessageHandler: (message: string) => void
};

const goalSection: FunctionComponent<GoalSectionProps> = (props) => {
    
    const {goals, collapseGoalHandler, toggleContextHandler, maxDepth, helpMessageHandler} = props;
    const firstGoalRef = useRef<HTMLDivElement>(null);
    
    useEffect(() => {
        scrollToBottomOfFirstGoal();
    }, [goals]);

    const scrollToBottomOfFirstGoal = () => {
        if(firstGoalRef.current) {
            firstGoalRef.current.scrollIntoView({
                // behavior: "smooth",
                block: "end",
                inline: "nearest"
            });
        }
    };
    
    const goalCollapsibles = goals.map((goal, index) => {
        
        if(index === 0) {
            return (
                <>
                    <CollapsibleGoalBlock 
                        goal={goal} goalIndex={index + 1} goalIndicator={index + 1 + " / " + goals.length} 
                        collapseHandler={collapseGoalHandler}
                        toggleContextHandler={toggleContextHandler}
                        helpMessageHandler={helpMessageHandler}
                        maxDepth={maxDepth}
                    />
                    <div ref={firstGoalRef}/>
                </>
            );
        }

        return (
            <CollapsibleGoalBlock 
                goal={goal} goalIndex={index + 1} goalIndicator={index + 1 + " / " + goals.length} 
                collapseHandler={collapseGoalHandler} 
                toggleContextHandler={toggleContextHandler}
                maxDepth={maxDepth} 
                helpMessageHandler={helpMessageHandler}
            />
        );
    });

    return (
        <div className={classes.Collapsibles}>
            {goalCollapsibles}
        </div>
    );
};

export default goalSection;