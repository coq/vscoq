import React, {useState, useCallback, useEffect} from 'react';
import { vscode } from "./utilities/vscode";
import { VSCodeButton } from "@vscode/webview-ui-toolkit/react";
import "./App.css";
import { DidChangeWorkspaceFoldersNotification } from 'vscode-languageclient';
import { PropertyStyleSheetBehavior } from '@microsoft/fast-foundation';

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

  const handleMessage = useCallback ((msg: any) => {
    switch (msg.data.command) {
      case 'renderProofView':
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
        <GoalPage goals={goals} collapseGoalHandler={collapseGoalHandler}/>
    </main>
  );
};

export default app;
