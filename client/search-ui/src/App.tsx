import React, {useState, useCallback, useEffect, KeyboardEventHandler, ChangeEventHandler, ChangeEvent} from 'react';
import { vscode } from "./utilities/vscode";
import { DidChangeWorkspaceFoldersNotification } from 'vscode-languageclient';
import { PropertyStyleSheetBehavior } from '@microsoft/fast-foundation';
import { v4 as uuid } from 'uuid';

import SearchPage from './components/templates/SearchPage';
import "./App.css";

type SearchResult = {
    id: string, 
    name: string,
    statement: string
};

const app = () => {
    
    const [searchString, setSearchString] = useState("");
    const [searchHistory, setSearchHistory] = useState<string[]>([]);
    const [historyIndex, setHistoryIndex] = useState(-1);
    const [searchResults, setSearchResults] = useState<Map<string, SearchResult[]>>(new Map([[uuid(), []]]));

    const handleMessage = useCallback ((msg: any) => {
        switch (msg.data.command) {
            case 'renderResult':
                const result = msg.data.text;
                setSearchResults(searchResults => {
                        
                    const newResults = new Map(searchResults);
                    //Typescript enforces we handle 'undefined' case
                    const oldSearchResult = searchResults.get(result.id) || [];
                    
                    newResults.set(
                        result.id, 
                        oldSearchResult.concat(result)
                    );
    
                    return newResults;
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
                
    
    const searchFieldInputHandler: ChangeEventHandler<HTMLInputElement> = (e) => {
        setSearchString(e.target.value);
    };

    const searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement> = (e) => {
            
        if(e.code === "Enter") {
            
            setSearchHistory(searchHistory => searchHistory.concat([searchString]));

            vscode.postMessage({
                command: "coqSearch",
                text: searchString,
            });

        }

        if(e.code === "ArrowUp") {

            if(searchHistory.length > historyIndex + 1) {
                setSearchString(searchHistory[historyIndex + 1]);
                setHistoryIndex(historyIndex + 1);
            }

        }

        if(e.code === "ArrowDown") {

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
    

    return (
        <main>
            <SearchPage
                value={searchString} 
                onTextInput={searchFieldInputHandler} 
                searchFieldKeyPressHandler={searchFieldKeyPressHandler} 
                copyNameHandler={copyNameToClipboard}
                results={searchResults}
            />
        </main>
    );
};

export default app;
