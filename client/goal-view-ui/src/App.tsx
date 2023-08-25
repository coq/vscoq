import React, {useState, useCallback, useEffect} from 'react';
import "./App.css";

import ProofViewPage from './components/templates/ProovViewPage';
import {Goal, ProofView, ProofViewKey} from './types';

const app = () => {

  const [proofView, setProofView] = useState<ProofView>(null);
  const [goalDisplaySetting, setGoalDisplaySetting] = useState<string>("List");

  const handleMessage = useCallback ((msg: any) => {
    switch (msg.data.command) {
        case 'initAppSettings':
            setGoalDisplaySetting(msg.data.text);
            break;
        case 'renderProofView':
            const proofView = msg.data.proofView;
            setProofView(proofView === null
                ? proofView
                : {
                    goals: proofView.goals.map((goal: Goal, index: number) => {
                        return {...goal, isOpen: index === 0, displayId: index+1 };
                    }),
                    shelvedGoals: proofView.shelvedGoals.map((goal: Goal, index: number) => {
                        return {...goal, isOpen: index === 0, displayId: index+1 };
                    }),
                    givenUpGoals: proofView.givenUpGoals.map((goal: Goal, index: number) => {
                        return {...goal, isOpen: index === 0, displayId: index+1 };
                    })
                }
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
            

    const collapseGoalHandler = (id: string, key: ProofViewKey) => {
        if(proofView) {
            if(proofView[key]) {
                const newGoals = proofView[key].map(goal => {
                    if(goal.id === id){
                        return {...goal, isOpen: !goal.isOpen};
                    }
                    return goal;
                });
                setProofView({
                    ...proofView, 
                    [key]: newGoals
                });
                
            }           
        }
    };

  return (
    <main>
        <ProofViewPage proofView={proofView} collapseGoalHandler={collapseGoalHandler} displaySetting={goalDisplaySetting}/>
    </main>
  );
};

export default app;
