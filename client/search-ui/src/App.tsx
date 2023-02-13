import React, {useState, useCallback, useEffect, KeyboardEventHandler, ChangeEventHandler, useRef} from 'react';
import { v4 as uuid } from 'uuid';

import SearchPage from './components/templates/SearchPage';
import "./App.css";

import { vscode } from "./utilities/vscode";

type QueryResult = {
    id: string, 
    type: string,
    name: string,
    statement: string
};

type SearchTab = {
    searchId: string, 
    searchString: string, 
    type: string, 
    results: QueryResult[],
};

const defaultTab = {
    searchId: uuid(), 
    searchString: "", 
    type: "Search",
    results: []
};

const defaultState = {
    searchString: "",
    searchHistory: [],
    historyIndex: -1, 
    searchTabs: [defaultTab],
    currentTab: 0
};

const app = () => {
    
    const [searchString, setSearchString] = useState("");
    const [searchHistory, setSearchHistory] = useState<string[]>([]);
    const [historyIndex, setHistoryIndex] = useState(-1);
    const [searchTabs, setSearchTabs] = useState<SearchTab[]>([defaultTab]);
    const [currentTab, setCurrentTab] = useState(0);
    const [queryType, setQueryType] = useState('Search');
    const firstUpdate = useRef(true);
    const restoringState = useRef(false);
    //this ref will allow us to update the current tab index only when the number of tabs has changed !
    const numTabs = useRef(1); 

    const handleMessage = useCallback ((msg: any) => {
        const result = msg.data.text;
        switch (msg.data.command) {
            case 'aboutResponse':
                setSearchTabs(searchTabs => { 
                    const newTabs = searchTabs.map(tab => {
                        if(tab.searchId === msg.data.id) {
                            return {...tab, results: [{id: "", name: "", statement: result, type: "About"}]};
                        }
                        return tab;
                    });
    
                    return newTabs;
                });
                break;
            case 'searchResponse':
                setSearchTabs(searchTabs => {
                    
                    const newTabs = searchTabs.map(tab => {
                        if(tab.searchId === result.id) {
                            return {...tab, results: tab.results.concat([{...result, type: "Search"}])};
                        }
                        return tab;
                    });
    
                    return newTabs;
                });
                break;
            case 'launchedSearch': 
                //TODO: Add UI elements to show user the searching state
                break;
        }
      }, []);
    
    useEffect(() => {
        window.addEventListener("message", handleMessage);
        return () => {
            window.removeEventListener("message", handleMessage);
        };
    }, [handleMessage]);
                    
    useEffect(() => {

        //Avoid use effect on first page load
        if(firstUpdate.current) {
            firstUpdate.current = false; 
            return;
        }

        //Avoid use effect when restoring a previous state
        if(restoringState.current) {
            restoringState.current = false; 
            numTabs.current = searchTabs.length;
            return;
        }

        //Did we add a tab ?
        if(numTabs.current < searchTabs.length) {
            numTabs.current = searchTabs.length;
            changeTabHandler(0);
            return;
        }

        //Did we remove a tab ?
        if(numTabs.current > searchTabs.length) {
            numTabs.current = searchTabs.length;
            if(currentTab > searchTabs.length - 1) {
                changeTabHandler(0); 
            }
            return;
        }

        //in any other situation just save the state
        saveState();
        
    }, [searchTabs, currentTab]);
    
    //this will only run on initial render
    useEffect(() => {
        //This is to avoid unecessary useEffect hook calls
        restoringState.current = true;
        restoreState();
    }, []);


    const queryTypeSelectHandler: ChangeEventHandler<HTMLInputElement> = (e) => {
        setQueryType(e.target.value);
    };

    const searchFieldInputHandler: ChangeEventHandler<HTMLInputElement> = (e) => {
        setSearchString(e.target.value);
    };

    const saveState = () => {
        vscode.setState({searchString, searchHistory, historyIndex, searchTabs, currentTab, queryType});
    };

    const restoreState = () => {
        const state: any = vscode.getState() || defaultState;
        setSearchTabs(state.searchTabs);
        setSearchHistory(state.searchHistory);
        setHistoryIndex(state.historyIndex);
        setSearchString(state.searchString);
        setCurrentTab(state.currentTab);
        setQueryType(state.queryType);
    };

    const searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement> = (e) => {
            
        if(e.code === "Enter") {
            
            setSearchHistory(searchHistory => [searchString].concat(searchHistory));
            
            const searchId = uuid();
            setSearchTabs(searchTabs => {
                const newTabs = searchTabs.map((tab, index) => {
                    if(index === currentTab) {
                        return {...tab, searchId: searchId, searchString, results: [], type: queryType};
                    }
                    return tab;
                });
                return newTabs;
            });

            vscode.postMessage({
                command: "coqQuery",
                text: searchString,
                id: searchId,
                type: queryType,
            });

        }

        if(e.code === "ArrowUp") {
            e.preventDefault();
            if(searchHistory.length > historyIndex + 1) {
                setSearchString(searchHistory[historyIndex + 1]);
                setHistoryIndex(historyIndex + 1);
            }

        }

        if(e.code === "ArrowDown") {
            e.preventDefault();
            if(historyIndex > -1) {
                if(historyIndex > 0) {
                    setSearchString(searchHistory[historyIndex - 1]);
                }
                setHistoryIndex(historyIndex - 1);
            }

        }

    };

    const copyNameToClipboard = (name: string) => {
        vscode.postMessage({
            command: "copySearchResult",
            text: name
        });
    };

    const addSearchTabHandler = () => {
        setSearchTabs(searchTabs => {
            //return searchTabs.concat([{searchId: uuid(), searchString: "", results: [], type: queryType}]);
            const results: QueryResult[] = [];
            return [{searchId: uuid(), searchString: "", results: results, type: queryType}].concat(searchTabs);
        });
    };

    const deleteSearchTabHandler = (tabIndex: number) => {
        setSearchTabs(searchTabs => {
            return searchTabs.filter((tab, index) => index !== tabIndex);
        });
    };
    
    const changeTabHandler = (tabIndex: number) => {
        setSearchString(searchTabs[tabIndex].searchString);
        setQueryType(searchTabs[tabIndex].type);
        setCurrentTab(tabIndex);
    };

    return (
        <main>
            <SearchPage
                value={searchString} 
                onTextInput={searchFieldInputHandler} 
                searchFieldKeyPressHandler={searchFieldKeyPressHandler} 
                copyNameHandler={copyNameToClipboard}
                tabs={searchTabs}
                addTabHandler={addSearchTabHandler}
                changeTabHandler={changeTabHandler}
                deleteTabHandler={deleteSearchTabHandler}
                currentTab={currentTab}
                queryTypeSelectHandler={queryTypeSelectHandler}
                selectedType={queryType}
            />
        </main>
    );
};

export default app;
