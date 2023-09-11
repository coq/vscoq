import React, {useState, useCallback, useEffect, KeyboardEvent, ChangeEventHandler, useRef, ChangeEvent} from 'react';
import { v4 as uuid } from 'uuid';

import SearchPage from './components/templates/SearchPage';
import "./App.css";

import { vscode } from "./utilities/vscode";
import { useStateCallback } from './utilities/hooks';

import { 
    Query,
    QueryError,
    QueryTab,
    QueryType,
    SearchNotification,
    QueryNotification,
    CheckResultType,
    AboutResultType,
    SearchResultType,
    LocateResultType,
    PrintResultType,
    QueryPanelState,
    VsCodeState,
} from './types';

const defaultTab = {
    id: uuid(),
    title: "New Tab",
    pattern: "", 
    type: QueryType.search,
    result: {
        type: QueryType.search,
        data: []
    } as SearchResultType,
    error: undefined,
    expanded: true
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

            case 'searchError': 
                handleError(msg.data.id, msg.data.error);
                break;

            case 'query':
                handleImmediateQueryNotification(msg.data.query);
                break;

            case 'addTab': 
                addTabHandler(); 
                break;

            case 'collapseAll': 
                collapseAll();
                break;

            case 'expandAll': 
                expandAll(); 
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
        ready();
    }, []);

    useEffect(() => {
        const {tabs, currentTab} = queryPanelState;
        if(tabs[currentTab].type === QueryType.search && 
            (tabs[currentTab].result as SearchResultType).data.length) {
            enableCollapseButton();
            updateCollapseButton(tabs[currentTab].expanded!);
        } else {
            disableCollapseButton();
        }

    }, [queryPanelState]);

    const ready = () => {
        vscode.postMessage({
            command: "ready",
        });
    };
    
    const handleError = (id: string, error: QueryError) => {
        setQueryPanelState(state => {

            const newTabs = state.tabs.map(tab => {
                if(tab.id === id) {
                    return {...tab, error: error} as QueryTab;
                }
                return tab; 
            });

            return {...state, tabs: newTabs};
        });
    };

    const handleSearchNotification = (notification : SearchNotification) => {        
        setQueryPanelState(state => {       

            const newTabs = state.tabs.map(tab => {
                if(tab.id === notification.id) {
                    //This is only for typescript, but should always be the case
                    if(tab.result.type === QueryType.search) { 
                        const data = tab.result.data.concat([{name: notification.name, statement: notification.statement, collapsed: false}]);
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

    const handleCheckNotification = (notification : QueryNotification) => {
        
        setQueryPanelState(state => { 
            const result = {type: QueryType.check, statement: notification.statement} as CheckResultType;
            const newTabs = state.tabs.map(tab => {
                if(tab.id === notification.id) {
                    return {...tab, result: result};
                }
                return tab;
            });

            return {...state, tabs: newTabs};
        }, (newState) => {
            saveState({state: newState, history, historyIndex});
        });

    };

    const handleAboutNotification = (notification : QueryNotification) => {
        
        setQueryPanelState(state => { 
            const result = {type: QueryType.about, statement: notification.statement} as AboutResultType;
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

    const handleLocateNotification = (notification: QueryNotification) => {
        
        setQueryPanelState(state => { 
            const result = {type: QueryType.locate, statement: notification.statement} as LocateResultType;
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

    const handlePrintNotification = (notification: QueryNotification) => {
        
        setQueryPanelState(state => { 
            const result = {type: QueryType.print, statement: notification.statement} as PrintResultType;
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
                return {type: QueryType.search, data: []} as SearchResultType;
            case QueryType.about:
                return {type: QueryType.about, statement: null} as AboutResultType;
            case QueryType.check:
                return {type: QueryType.check, statement: null} as CheckResultType;
            case QueryType.locate:
                return {type: QueryType.locate, statement: null} as LocateResultType;
            case QueryType.print: 
                return {type: QueryType.print, statement: null} as PrintResultType;
        }
    };

    const handleImmediateQueryNotification = (notification: Query) => {
        const {pattern, type} = notification;
        const result = initResult(type);
        const id = uuid();
        const newTab : QueryTab[] = [{id: id, title: type + ": " + pattern, pattern: pattern, result: result, type: type}];
        setQueryPanelState(state => {
            const newTabs = state.tabs.concat(newTab);
            return {currentTab: newTabs.length - 1, tabs: newTabs};
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
                    return {...tab, id: id, error: undefined, result: initResult(type), title: type + ": " + pattern};
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

    const updateCollapseButton = (buttonStatus: boolean) => {
        vscode.postMessage({
            command: "toggleExpandButton", 
            value: buttonStatus
        });
    };

    const enableCollapseButton = () => {
        vscode.postMessage({
            command: "enableCollapseButton"
        });
    };

    const disableCollapseButton = () => {
        vscode.postMessage({
            command: "disableCollapseButton"
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
                const result = {type: QueryType.search, data: []} as SearchResultType; 
                const newTab : QueryTab[] = [{id: uuid(), title: "New Tab", pattern: "", result: result, type: QueryType.search, expanded: true}];
                return {currentTab: state.tabs.length, tabs: state.tabs.concat(newTab)};
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
            (state) => {
                saveState({state, history, historyIndex});
            }
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

    const collapseAll = () => {
        setQueryPanelState(state => {
            const newTabs = state.tabs.map((tab, index) => {
                if(index === state.currentTab && tab.result.type === 'search') {
                    const data = tab.result.data.map(r => {
                        return {...r, collapsed: true};
                    });
                    const result = {
                        type: QueryType.search, 
                        data: data
                    } as SearchResultType;
                    return {...tab, result: result, expanded: false};
                }
                return tab;
            });
            return {...state, tabs: newTabs};
        });
    };
    
    const expandAll = () => {
        setQueryPanelState(state => {
            const newTabs = state.tabs.map((tab, index) => {
                if(index === state.currentTab && tab.result.type === QueryType.search) {
                    const data = tab.result.data.map(r => {
                        return {...r, collapsed: false};
                    });
                    const result = {
                        type: "search", 
                        data: data
                    } as SearchResultType;
                    return {...tab, result: result, expanded: true};
                }
                return tab;
            });
            return {...state, tabs: newTabs};
        });
    };

    const toggleSearchResultDefinition = (index: number) => {
        setQueryPanelState(state => {
            const newTabs = state.tabs.map((tab, i) => {
                if(i === state.currentTab && tab.result.type === QueryType.search) {
                    const data = tab.result.data.map((r,i) => {
                        if(i === index) {
                            return {...r, collapsed: !r.collapsed};
                        }
                        return r;
                    });
                    return {...tab, result: {...tab.result, data: data}};
                }
                return tab; 
            });
            return {...state, tabs: newTabs};
        });
    };

    const deleteSearchResultHandler = (index: number) => {
        setQueryPanelState(state => {
            const newTabs = state.tabs.map((tab, i) => {
                if(i === state.currentTab && tab.result.type === QueryType.search) {
                    const data = tab.result.data.filter((r,i) => i !== index);
                    return {...tab, result: {...tab.result, data: data}};
                }
                return tab; 
            });
            return {...state, tabs: newTabs};
        });
    };
    
    return (
        <main>
            <SearchPage
                state={queryPanelState}
                searchFieldKeyPressHandler={searchFieldKeyPressHandler} 
                copyNameHandler={copyNameToClipboard}
                toggleCollapsedHandler={toggleSearchResultDefinition}
                deleteSearchResultHander={deleteSearchResultHandler}
                addTabHandler={addTabHandler}
                changeTabHandler={changeTabHandler}
                deleteTabHandler={deleteTabHandler}
                tabInputHandler={tabInputHandler}
            />
        </main>
    );
};

export default app;
