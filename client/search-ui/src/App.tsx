import React, {useState, useCallback, useEffect, KeyboardEventHandler, ChangeEventHandler, useRef} from 'react';
import { DidChangeWorkspaceFoldersNotification, StarNotificationHandler } from 'vscode-languageclient';
import { PropertyStyleSheetBehavior } from '@microsoft/fast-foundation';
import { v4 as uuid } from 'uuid';

import SearchPage from './components/templates/SearchPage';
import "./App.css";

import { vscode } from "./utilities/vscode";

type SearchResult = {
    id: string, 
    name: string,
    statement: string
};

type SearchTab = {
    searchId: string, 
    searchString: string, 
    results: SearchResult[]
};

const defaultTab = {
    searchId: uuid(), 
    searchString: "", 
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
    const firstUpdate = useRef(true);
    //this ref will allow us to update the current tab index only when the number of tabs has changed !
    const numTabs = useRef(1); 

    const handleMessage = useCallback ((msg: any) => {
        switch (msg.data.command) {
            case 'renderResult':
                const result = msg.data.text;
                setSearchTabs(searchTabs => {
                    
                    const newTabs = searchTabs.map(tab => {
                        if(tab.searchId === result.id) {
                            return {...tab, results: tab.results.concat([result])};
                        }
                        return tab;
                    });
    
                    return newTabs;
                });
                break;
            case 'searching': 
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
        if(firstUpdate.current) {
            firstUpdate.current = false; 
            return;
        }
        //check if the num of tabs has changed
        if(numTabs.current < searchTabs.length) {
            changeTabHandler(searchTabs.length - 1);
            numTabs.current = searchTabs.length;
        }
        if(numTabs.current > searchTabs.length) {
            if(currentTab > searchTabs.length - 1) {
                changeTabHandler(searchTabs.length - 1);
            }
            numTabs.current = searchTabs.length;
        }
        saveState();
    }, [searchTabs]);
    
    //this will only run on initial render
    useEffect(() => {
        restoreState();
    }, []);

    const searchFieldInputHandler: ChangeEventHandler<HTMLInputElement> = (e) => {
        setSearchString(e.target.value);
    };

    const saveState = () => {
        vscode.setState({searchString, searchHistory, historyIndex, searchTabs, currentTab});
    };

    const restoreState = () => {
        const state: any = vscode.getState() || defaultState;
        setSearchTabs(state.searchTabs);
        setSearchHistory(state.searchHistory);
        setHistoryIndex(state.historyIndex);
        setSearchString(state.searchString);
        setCurrentTab(state.currentTab);
    };

    const searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement> = (e) => {
            
        if(e.code === "Enter") {
            
            setSearchHistory(searchHistory => [searchString].concat(searchHistory));
            
            const searchId = uuid();
            setSearchTabs(searchTabs => {
                const newTabs = searchTabs.map((tab, index) => {
                    if(index === currentTab) {
                        return {...tab, searchId: searchId, results: []};
                    }
                    return tab;
                });
                return newTabs;
            });

            vscode.postMessage({
                command: "coqSearch",
                text: searchString,
                id: searchId,
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
            return searchTabs.concat([{searchId: uuid(), searchString: "", results: []}]);
        });
    };

    const deleteSearchTabHandler = (tabIndex: number) => {
        setSearchTabs(searchTabs => {
            return searchTabs.filter((tab, index) => index !== tabIndex);
        });
    };
    
    const changeTabHandler = (tabIndex: number) => {
        setSearchString(searchTabs[tabIndex].searchString);
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
            />
        </main>
    );
};

export default app;
