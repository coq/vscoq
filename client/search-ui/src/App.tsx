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
    CheckResultType,
    AboutResultType,
    SearchResultType,
    LocateNotification, 
    LocateResultType,
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
}

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
        }
    }

    const handleImmediateQueryNotification = (notification: Query) => {
        setQueryPanelState(state => {
            const result = initResult(notification.type);
            const newTab : QueryTab[] = [{id: uuid(), pattern: notification.pattern, result: result, type: notification.type}];
            return {currentTab: 0, tabs: newTab.concat(state.tabs)};
        }, (newState) => {
            const {pattern, id, type} = newState.tabs[0];
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

    const launchQuery = () => {

        const {pattern, type} = queryPanelState.tabs[queryPanelState.currentTab];
            
        setHistory(history => [pattern].concat(history));
            
        const id = uuid();
        setQueryPanelState(state => {
            const newTabs = state.tabs.map((tab, index) => {
                if(index === state.currentTab) {
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
            />
        </main>
    );
};

export default app;
