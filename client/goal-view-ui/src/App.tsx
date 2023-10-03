import React, {useState, useCallback, useEffect} from 'react';
import "./App.css";

import ProofViewPage from './components/templates/ProovViewPage';
import {Goal, ProofViewGoals, ProofViewGoalsKey, ProofViewMessage} from './types';

const app = () => {

  const [goals, setGoals] = useState<ProofViewGoals>(null);
  const [messages, setMessages] = useState<ProofViewMessage[]>([]);
  const [goalDisplaySetting, setGoalDisplaySetting] = useState<string>("List");

  const handleMessage = useCallback ((msg: any) => {
    switch (msg.data.command) {
        case 'initAppSettings':
            setGoalDisplaySetting(msg.data.text);
            break;
        case 'renderProofView':
            const allGoals = msg.data.proofView.proof;
            const messages = msg.data.proofView.messages;
            setMessages(messages);
            setGoals(allGoals === null
                ? allGoals
                : {
                    main: allGoals.goals.map((goal: Goal, index: number) => {
                        return {...goal, isOpen: index === 0};
                    }),
                    shelved: allGoals.shelvedGoals.map((goal: Goal, index: number) => {
                        return {...goal, isOpen: index === 0};
                    }),
                    givenUp: allGoals.givenUpGoals.map((goal: Goal, index: number) => {
                        return {...goal, isOpen: index === 0}; 
                    })
                }
            );
            break;
        case 'reset':
            setMessages([]);
            setGoals(null);
            break;
    }
  }, []);

    useEffect(() => {
        window.addEventListener("message", handleMessage);
        return () => {
            window.removeEventListener("message", handleMessage);
        };
    }, [handleMessage]);
            

    const collapseGoalHandler = (id: string, key: ProofViewGoalsKey) => {
        const newGoals = goals![key].map(goal => {
            if(goal.id === id){
                return {...goal, isOpen: !goal.isOpen};
            }
            return goal;
        });
        setGoals({
            ...goals!, 
            [key]: newGoals
        });          
    };

  return (
    <main>
        <ProofViewPage goals={goals} messages={messages} collapseGoalHandler={collapseGoalHandler} displaySetting={goalDisplaySetting}/>
    </main>
  );
};

export default app;
