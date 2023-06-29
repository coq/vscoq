import React, {useState, useCallback, useEffect, KeyboardEvent, ChangeEventHandler, useRef, ChangeEvent} from 'react';
import { v4 as uuid } from 'uuid';

import SearchPage from './components/templates/SearchPage';
import "./App.css";

import { vscode } from "./utilities/vscode";
import { useStateCallback } from './utilities/hooks';

import { 
    Query, 
    QueryTab, 
    QueryType, 
    SearchNotification,
    AboutNotification,
    CheckNotification,
    CheckResultType,
    AboutResultType,
    SearchResultType,
    LocateNotification, 
    LocateResultType,
    PrintNotification, 
    PrintResultType,
    QueryPanelState, 
    VsCodeState,
} from './types';

const defaultTab = {
    id: uuid(), 
    pattern: "", 
    type: QueryType.search,
    result: {
        type: "search", 
        data: []
    } as SearchResultType
};

const defaultQueryPanelState = {
    currentTab: 0, 
    tabs: [defaultTab]
};

const defaultState = {
    history: [],
    historyIndex: -1, 
    queryPanelState: defaultQueryPanelState
};

const app = () => {
    
    const [history, setHistory] = useState<string[]>([]);
    const [historyIndex, setHistoryIndex] = useState(-1);
    const [queryPanelState, setQueryPanelState] = useStateCallback<QueryPanelState>(defaultQueryPanelState);

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

            case 'locateResponse': 
                handleLocateNotification(msg.data.result);
                break;

            case 'printResponse':
                handlePrintNotification(msg.data.result);

            case 'launchedSearch': 
                //TODO: Add UI elements to show user the searching state
                break;

            case 'query':
                handleImmediateQueryNotification(msg.data.query);
                break;

            case 'addTab': 
                addTabHandler(); 
                break;
                
        }
      }, []);
    
    useEffect(() => {
        window.addEventListener("message", handleMessage);
        return () => {
            window.removeEventListener("message", handleMessage);
        };
    }, [handleMessage]);

    //this will only run on initial render
    useEffect(() => {
        restoreState();
    }, []);

    const handleSearchNotification = (notification : SearchNotification) => {        
        setQueryPanelState(state => {       

            const newTabs = state.tabs.map(tab => {
                if(tab.id === notification.id) {
                    //Here this should always be the case since the tab was initialized as a search
                    if(tab.result.type === "search") {
                        const data = tab.result.data.concat([{name: notification.name, statement: notification.statement}]);
                        return {...tab, result: {...tab.result, data: data}};
                    }
                }
                return tab;
            });
            return {...state, tabs: newTabs};
        }, (newState) => {
            saveState({state: newState, history, historyIndex});
        });
    };

    const handleCheckNotification = (notification : CheckNotification) => {
        
        setQueryPanelState(state => { 
            const result = {type: "check", statement: notification.statement} as CheckResultType;
            const newTabs = state.tabs.map(tab => {
                if(tab.id === notification.id) {
                    if(tab.result.type === "check") {                        
                        return {...tab, result: result};
                    }
                }
                return tab;
            });

            return {...state, tabs: newTabs};
        }, (newState) => {
            saveState({state: newState, history, historyIndex});
        });

    };

    const handleAboutNotification = (notification : AboutNotification) => {
        
        setQueryPanelState(state => { 
            const result = {type: "about", statement: notification.statement} as AboutResultType;
            const newTabs = state.tabs.map(tab => {
                if(tab.id === notification.id) {
                    return {...tab, result: result};
                }
                return tab;
            });

            return {...state, tabs: newTabs};
        }, (newState) => {
            saveState({state: newState, history, historyIndex});
        } );

    };

    const handleLocateNotification = (notification: LocateNotification) => {
        
        setQueryPanelState(state => { 
            const result = {type: "locate", statement: notification.statement} as LocateResultType;
            const newTabs = state.tabs.map(tab => {
                if(tab.id === notification.id) {
                    return {...tab, result: result};
                }
                return tab;
            });

            return {...state, tabs: newTabs};
        }, (newState) => {
            saveState({state: newState, history, historyIndex});
        } );

    };

    const handlePrintNotification = (notification: PrintNotification) => {
        
        setQueryPanelState(state => { 
            const result = {type: "print", statement: notification.statement} as PrintResultType;
            const newTabs = state.tabs.map(tab => {
                if(tab.id === notification.id) {
                    return {...tab, result: result};
                }
                return tab;
            });

            return {...state, tabs: newTabs};
        }, (newState) => {
            saveState({state: newState, history, historyIndex});
        } );

    };

    const initResult = (type: QueryType) => {
        switch (type) {
            case QueryType.search:
                return {type: "search", data: []} as SearchResultType;
            case QueryType.about:
                return {type: "about", statement: ""} as AboutResultType;
            case QueryType.check:
                return {type: "check", statement: ""} as CheckResultType;
            case QueryType.locate:
                return {type: "locate", statement: ""} as LocateResultType;
            case QueryType.print: 
                return {type: "print", statement: ""} as PrintResultType;
        }
    };

    const handleImmediateQueryNotification = (notification: Query) => {
        const {pattern, type} = notification;
        const result = initResult(type);
        const id = uuid();
        const newTab : QueryTab[] = [{id: id, pattern: pattern, result: result, type: type}];
        setQueryPanelState(state => {
            const newTabs = newTab.concat(state.tabs);
            return {currentTab: 0, tabs: newTabs};
        }, () => {
            vscode.postMessage({
                command: "coqQuery",
                text: pattern,
                id: id,
                type: type,
            });
        });
    };

    const saveState = (state: VsCodeState) => {
        vscode.setState(state);
    };

    const restoreState = () => {
        const state: VsCodeState = vscode.getState() || defaultState;
        if(state.state) {setQueryPanelState(state.state);}
        if(state.history) {setHistory(state.history);}
        if(state.historyIndex) {setHistoryIndex(state.historyIndex);}
    };

    const launchQuery = (index: number) => {

        const {pattern, type} = queryPanelState.tabs[index];
            
        setHistory(history => [pattern].concat(history));
            
        const id = uuid();
        setQueryPanelState(state => {
            const newTabs = state.tabs.map((tab, i) => {
                if(index === i) {
                    return {...tab, id: id, result: initResult(type)};
                }
                return tab;
            });
            return {...state, tabs: newTabs};
        });

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

    const searchFieldKeyPressHandler: ((index:number, e: KeyboardEvent<HTMLInputElement>) => void) = (index, e) => {
            
        if(e.code === "Enter") {
            launchQuery(index);
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

    const tabInputHandler: ((index: number, field: string) => (ChangeEventHandler<HTMLInputElement>)) = (index: number, field: string) => {
        return (e: ChangeEvent<HTMLInputElement>) => {
            setQueryPanelState(state => {
                const newTabs = state.tabs.map((tab, i) => {
                    if(index === i) {
                        return {...tab, [field]: e.target.value};
                    }
                    return tab;
                });
                return {...state, tabs: newTabs};
            });
        };
    };
    
    const updateQueryType = (type: QueryType) => {
        setQueryPanelState(state => {
            const newTabs = state.tabs.map((tab, index) => {
                if(index === state.currentTab) {
                    return {...tab, type: type};
                }
                return tab;
            });
            return {...state, tabs: newTabs};
        });
    };

    const updateQueryString = (pattern: string) => {
        setQueryPanelState(state => {
            const newTabs = state.tabs.map((tab, index) => {
                if(index === state.currentTab) {
                    return {...tab, pattern: pattern};
                }
                return tab;
            });
            return {...state, tabs: newTabs};
        });
    };

    const copyNameToClipboard = (name: string) => {
        vscode.postMessage({
            command: "copySearchResult",
            text: name
        });
    };

    const addTabHandler = () => {
        setQueryPanelState(
            state => {
                const result = {type: "search", data: []} as SearchResultType; 
                const newTab : QueryTab[] = [{id: uuid(), pattern: "", result: result, type: QueryType.search}];
                return {currentTab: 0, tabs: newTab.concat(state.tabs)};
            }, 
            (state) => saveState({state, history, historyIndex})
        );
    };

    const deleteTabHandler = (tabIndex: number) => {

        setQueryPanelState(
            state => {
                const newTabs = state.tabs.filter((tab, index) => index !== tabIndex);
                if(state.currentTab < newTabs.length) {
                    return {...state, tabs: newTabs};
                }
                else {
                    return {currentTab: state.currentTab - 1, tabs: newTabs} as QueryPanelState;
                }
                
            }, 
            (state) => saveState({state, history, historyIndex})
        );
    };
    
    const changeTabHandler = (tabIndex: number) => {
        setQueryPanelState(
            state => {
                return {...state, currentTab: tabIndex};
            },
            state => saveState({state, history, historyIndex})
        );
    };

    return (
        <main>
            <SearchPage
                state={queryPanelState}
                onTextInput={searchFieldInputHandler} 
                searchFieldKeyPressHandler={searchFieldKeyPressHandler} 
                copyNameHandler={copyNameToClipboard}
                addTabHandler={addTabHandler}
                changeTabHandler={changeTabHandler}
                deleteTabHandler={deleteTabHandler}
                queryTypeSelectHandler={queryTypeSelectHandler}
                tabInputHandler={tabInputHandler}
            />
        </main>
    );
};

export default app;
