import React, {useState, useCallback, useEffect, KeyboardEventHandler, ChangeEventHandler, ChangeEvent} from 'react';
import { vscode } from "./utilities/vscode";
import { VSCodeButton } from "@vscode/webview-ui-toolkit/react";
import "./App.css";
import { DidChangeWorkspaceFoldersNotification } from 'vscode-languageclient';
import { PropertyStyleSheetBehavior } from '@microsoft/fast-foundation';
import SearchField from './components/molecules/SearchField';

const app = () => {
    
    const [searchString, setSearchString] = useState("");

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
    

    return (
        <main>
            <SearchField 
                value={searchString} 
                onTextInput={searchFieldInputHandler} 
                handleSearch={searchFieldEnterHandler} 
            />
        </main>
    );
};

export default app;
