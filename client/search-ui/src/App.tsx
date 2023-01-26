import React, {useState, useCallback, useEffect} from 'react';
import { vscode } from "./utilities/vscode";
import { VSCodeButton } from "@vscode/webview-ui-toolkit/react";
import "./App.css";
import { DidChangeWorkspaceFoldersNotification } from 'vscode-languageclient';
import { PropertyStyleSheetBehavior } from '@microsoft/fast-foundation';

const app = () => {


  return (
    <main>
        <VSCodeButton>
            Search
        </VSCodeButton>
    </main>
  );
};

export default app;
