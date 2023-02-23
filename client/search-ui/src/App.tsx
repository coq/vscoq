import React, {useState, useCallback, useEffect, KeyboardEventHandler, ChangeEventHandler, useRef} from 'react';
import { v4 as uuid } from 'uuid';

import SearchPage from './components/templates/SearchPage';
import "./App.css";

import { vscode } from "./utilities/vscode";
import { useStateCallback } from './utilities/hooks';

import { 
    Query, 
    QueryResult, 
    QueryTab, 
    QueryType, 
    SearchNotification,
    AboutNotification,
    CheckNotification,
} from './types';

const defaultTab = {
    id: uuid(), 
    pattern: "", 
    type: QueryType.search,
    results: []
};

const defaultState = {
    history: [],
    historyIndex: -1, 
    tabs: [defaultTab],
    currentTab: 0
};

const app = () => {
    
    const [history, setHistory] = useState<string[]>([]);
    const [historyIndex, setHistoryIndex] = useState(-1);
    const [tabs, setTabs] = useStateCallback<QueryTab[]>([defaultTab]);
    const [currentTab, setCurrentTab] = useStateCallback(0);
    const restoringState = useRef(false);
    const immediateQuery = useRef(false);


    const handleMessage = useCallback ((msg: any) => {
        switch (msg.data.command) {

            case 'checkResponse':
                handleCheckNotification(msg.data.result);
                break;

            case 'aboutResponse':
                handleAboutNotification(msg.data.result);
                break;

            case 'searchResponse':
                handleSearchNotification(msg.data.result); 
                break;

            case 'launchedSearch': 
                //TODO: Add UI elements to show user the searching state
                break;

            case 'query':
                handleImmediateQueryNotification(msg.data.query);
                break;
        }
      }, []);
    
    useEffect(() => {
        window.addEventListener("message", handleMessage);
        return () => {
            window.removeEventListener("message", handleMessage);
        };
    }, [handleMessage]);
/* 
    //this will only run on initial render
    useEffect(() => {
        //This is to avoid unecessary useEffect hook calls
        restoringState.current = true;
        restoreState();
    }, []);
     */

    const handleSearchNotification = (notification : SearchNotification) => {
        
        setTabs((tabs: QueryTab[]) => {       

            const newTabs = tabs.map(tab => {
                if(tab.id === notification.id) {
                    //Here this should always be the case since the tab was initialize as a search
                    if(Array.isArray(tab.results)) {
                        return {...tab, results: tab.results.concat([{name: notification.name, statement: notification.statement}])};
                    }
                    return tab;
                }
                return tab;
            });

            return newTabs;
        });
    };

    const handleCheckNotification = (notification : CheckNotification) => {
        
        setTabs(tabs => { 
            const newTabs = tabs.map(tab => {
                if(tab.id === notification.id) {
                    return {...tab, results: notification.statement};
                }
                return tab;
            });

            return newTabs;
        });

    };

    const handleAboutNotification = (notification : AboutNotification) => {
        
        setTabs(tabs => { 
            const newTabs = tabs.map(tab => {
                if(tab.id === notification.id) {
                    return {...tab, results: notification.statement};
                }
                return tab;
            });

            return newTabs;
        });

    };

    const handleImmediateQueryNotification = (notification: Query) => {
        
        setTabs(tabs => {
            const results : QueryResult = notification.type === QueryType.search ?  [] : "";
            const newTab : QueryTab[] = [{id: uuid(), pattern: notification.pattern, results: results, type: notification.type}];
            return newTab.concat(tabs);
        });
    };

    const saveState = () => {
        vscode.setState({history, historyIndex, tabs, currentTab});
    };

    const restoreState = () => {
        const state: any = vscode.getState() || defaultState;
        setTabs(state.searchTabs);
        setHistory(state.history);
        setHistoryIndex(state.historyIndex);
        setCurrentTab(state.currentTab);
    };

    const launchQuery = () => {

        const {pattern, type} = tabs[currentTab];
            
        setHistory(history => [pattern].concat(history));
            
        const id = uuid();
        setTabs(tabs => {
            const newTabs = tabs.map((tab, index) => {
                if(index === currentTab) {
                    return {...tab, id: id, results: []};
                }
                return tab;
            });
            return newTabs;
        }, 
        //after setting the new state we save the current state
        saveState);

        vscode.postMessage({
            command: "coqQuery",
            text: pattern,
            id: id,
            type: type,
        });

    };

    const queryTypeSelectHandler: ChangeEventHandler<HTMLInputElement> = (e) => {
        updateQueryType(QueryType[e.target.value as keyof typeof QueryType]);
    };

    const searchFieldInputHandler: ChangeEventHandler<HTMLInputElement> = (e) => {
        updateQueryString(e.target.value);
    };

    const searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement> = (e) => {
            
        if(e.code === "Enter") {
            launchQuery();
        }

        if(e.code === "ArrowUp") {
            e.preventDefault();
            if(history.length > historyIndex + 1) {
                updateQueryString(history[historyIndex + 1]);
                setHistoryIndex(historyIndex + 1);
            }

        }

        if(e.code === "ArrowDown") {
            e.preventDefault();
            if(historyIndex > -1) {
                if(historyIndex > 0) {
                    updateQueryString(history[historyIndex -1]);
                }
                setHistoryIndex(historyIndex - 1);
            }

        }

    };

    
    const updateQueryType = (type: QueryType) => {
        setTabs(tabs => {
            return tabs.map((tab, index) => {
                if(index === currentTab) {
                    return {...tab, type: type};
                }
                return tab;
            });
        });
    };

    const updateQueryString = (pattern: string) => {
        setTabs(tabs => {
            return tabs.map((tab, index) => {
                if(index === currentTab) {
                    return {...tab, pattern: pattern};
                }
                return tab;
            });
        });
    };

    const copyNameToClipboard = (name: string) => {
        vscode.postMessage({
            command: "copySearchResult",
            text: name
        });
    };

    const addSearchTabHandler = () => {
        setTabs(
            tabs => {
                const results : QueryResult = [];
                const newTab : QueryTab[] = [{id: uuid(), pattern: "", results: results, type: QueryType.search}];
                return newTab.concat(tabs);
            }, 
            () => setCurrentTab(0)
        );
    };

    const deleteSearchTabHandler = (tabIndex: number) => {
        setTabs(
            tabs => {
                return tabs.filter((tab, index) => index !== tabIndex);
            },
            (newTabs) => {
                if(currentTab > newTabs.length) {
                    setCurrentTab(newTabs.length - 1, saveState); 
                }
                else {
                    saveState();
                }
            }
        );
    };
    
    const changeTabHandler = (tabIndex: number) => {
        setCurrentTab(tabIndex, saveState);
    };

    return (
        <main>
            <SearchPage
                tabs={tabs}
                currentTab={currentTab}
                onTextInput={searchFieldInputHandler} 
                searchFieldKeyPressHandler={searchFieldKeyPressHandler} 
                copyNameHandler={copyNameToClipboard}
                addTabHandler={addSearchTabHandler}
                changeTabHandler={changeTabHandler}
                deleteTabHandler={deleteSearchTabHandler}
                queryTypeSelectHandler={queryTypeSelectHandler}
            />
        </main>
    );
};

export default app;
