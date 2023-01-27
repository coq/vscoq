import React, {useState, useCallback, useEffect, KeyboardEventHandler, ChangeEventHandler, ChangeEvent} from 'react';
import { vscode } from "./utilities/vscode";
import "./App.css";
import { DidChangeWorkspaceFoldersNotification } from 'vscode-languageclient';
import { PropertyStyleSheetBehavior } from '@microsoft/fast-foundation';
import SearchField from './components/molecules/SearchField';
import SearchPage from './components/templates/SearchPage';

type SearchResult = {
    id: string, 
    name: string,
    statement: string
};

const defaultResults = [
        {
            id: "1",
            name: "False_rect", 
            statement: "forall P : Type, False -> P", 
        },
        {
            id: "1",
            name: "False_ind", 
            statement: "forall P : Prop, False -> P", 
        }
    ];

const app = () => {
    
    const [searchString, setSearchString] = useState("");
    const [searchResults, setSearchResults] = useState<SearchResult[]>(defaultResults);

    const handleMessage = useCallback ((msg: any) => {
        switch (msg.data.command) {
            case 'renderResult':
                const result = msg.data.txt;
                setSearchResults(searchResults.concat([msg.data.txt]));
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

    const searchFieldEnterHandler: KeyboardEventHandler<HTMLInputElement> = (e) => {
            
        if(e.code === "Enter") {
            
            vscode.postMessage({
                command: "coqSearch",
                text: searchString,
            });

        }

    };

    const copyNameToClipboard = (name: string) => {

    };
    

    return (
        <main>
            <SearchPage
                value={searchString} 
                onTextInput={searchFieldInputHandler} 
                handleSearch={searchFieldEnterHandler} 
                copyNameHandler={copyNameToClipboard}
                results={searchResults}
            />
        </main>
    );
};

export default app;
