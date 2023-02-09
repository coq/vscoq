import React, {useState, useCallback, useEffect} from 'react';
import "./App.css";

import GoalPage from './components/templates/GoalPage';


type Goal = {
    id: string,
    goal: string, 
    hypotheses: {
        identifiers: string[],
        type: string
    }[],
    isOpen: boolean, 
    displayId: number
};

const app = () => {

  const [goals, setGoals] = useState<Goal[]>([]);
  const [isInProof, setIsInProof] = useState(false);
  const [goalDisplaySetting, setGoalDisplaySetting] = useState<string>("List");

  const handleMessage = useCallback ((msg: any) => {
    switch (msg.data.command) {
      case 'initAppSettings':
        setGoalDisplaySetting(msg.data.text);
        break;
      case 'renderProofView':
        setIsInProof(msg.data.text.isInProof);
        setGoals(msg.data.text.goals.map((goal: Goal, index: number) => {
            return {...goal, isOpen: index === 0, displayId: index+1 };
        }));
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
        const newGoals = goals.map(goal => {
            if(goal.id === id){
                return {...goal, isOpen: !goal.isOpen};
            }
            return goal;
        });
        setGoals(newGoals);
    };

  return (
    <main>
        <GoalPage goals={goals} collapseGoalHandler={collapseGoalHandler} displaySetting={goalDisplaySetting} isInProof={isInProof} />
    </main>
  );
};

export default app;
