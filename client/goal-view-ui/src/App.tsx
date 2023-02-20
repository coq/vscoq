import React, {useState, useCallback, useEffect} from 'react';
import "./App.css";

import GoalPage from './components/templates/GoalPage';
import {Goal, GoalArrayOrNull} from './types';

const app = () => {

  const [goals, setGoals] = useState<GoalArrayOrNull>(null);
  const [goalDisplaySetting, setGoalDisplaySetting] = useState<string>("List");

  const handleMessage = useCallback ((msg: any) => {
    switch (msg.data.command) {
        case 'initAppSettings':
            setGoalDisplaySetting(msg.data.text);
            break;
        case 'renderProofView':
            const proofView = msg.data.proofView;
            setGoals(proofView === null 
                ? null 
                : proofView.goals.map((goal: Goal, index: number) => {
                    return {...goal, isOpen: index === 0, displayId: index+1 };
                })
            );
            break;
    }
  }, []);

    useEffect(() => {
        window.addEventListener("message", handleMessage);
        return () => {
            window.removeEventListener("message", handleMessage);
        };
    }, [handleMessage]);
            

    const collapseGoalHandler = (id: string) => {
        if(goals) {
            const newGoals = goals.map(goal => {
                if(goal.id === id){
                    return {...goal, isOpen: !goal.isOpen};
                }
                return goal;
            });
            setGoals(newGoals);
        }
    };

  return (
    <main>
        <GoalPage goals={goals} collapseGoalHandler={collapseGoalHandler} displaySetting={goalDisplaySetting} />
    </main>
  );
};

export default app;
