import React, {useState, useCallback, useEffect} from 'react';
import { vscode } from "./utilities/vscode";
import { VSCodeButton } from "@vscode/webview-ui-toolkit/react";
import "./App.css";
import { DidChangeWorkspaceFoldersNotification } from 'vscode-languageclient';
import { PropertyStyleSheetBehavior } from '@microsoft/fast-foundation';

import Goal from './components/atoms/Goal';
import HypothesesBlock from './components/molecules/HypothesesBlock';
import GoalBlock from './components/molecules/GoalBlock';
import GoalSection from './components/organisms/GoalSection';


type Goal = {
    id: string,
    goal: string, 
    hypotheses: {
        identifiers: string[],
        type: string
    }[]
};

const app = () => {

  const [goals, setGoals] = useState<Goal[]>([]);

  const handleMessage = useCallback ((msg: any) => {
    switch (msg.data.command) {
      case 'renderProofView':
        setGoals(msg.data.text.goals);
        break;
    }
  }, []);

    useEffect(() => {
        window.addEventListener("message", handleMessage);
        return () => {
            window.removeEventListener("message", handleMessage);
        };
    }, [handleMessage]);
            
    
    console.log("goals should be an array", goals);
  return (
    <main>
        <GoalSection goals={goals} />
    </main>
  );
};

export default app;
