import {
    TextEditor,
    commands
} from 'vscode';

import {
    RequestType,
    VersionedTextDocumentIdentifier,
} from 'vscode-languageclient/node';

import GoalPanel from './panels/GoalPanel';

import Client from './client';
import { InterpretToPointRequest, UpdateProofViewResponse } from './protocol/types';

export const sendInterpretToPoint = (editor: TextEditor,  client: Client) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    const textDocument = VersionedTextDocumentIdentifier.create(uri.toString(), version);
    const position = editor.selection.active;
    
    const req = new RequestType<InterpretToPointRequest, UpdateProofViewResponse, void>("vscoq/interpretToPoint");
    const params: InterpretToPointRequest = {textDocument, position};

    if(!GoalPanel.currentPanel) {commands.executeCommand('vscoq.displayGoals'); };

    client.sendRequest(req, params).then(
        (response: UpdateProofViewResponse) => {
            GoalPanel.handleProofViewResponse(response);
        }
    );/* 
    client.sendNotification("vscoq/interpretToPoint", {textDocument: textDocument, position: position}); */
};

export const sendInterpretToEnd = (editor: TextEditor,  client: Client) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    const textDocument = VersionedTextDocumentIdentifier.create(uri.toString(), version);
    if(!GoalPanel.currentPanel) {commands.executeCommand('vscoq.displayGoals'); };
    client.sendNotification("vscoq/interpretToEnd", {textDocument: textDocument});
};

export const sendStepForward = (editor: TextEditor,  client: Client) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    const textDocument = VersionedTextDocumentIdentifier.create(uri.toString(), version);
    if(!GoalPanel.currentPanel) {commands.executeCommand('vscoq.displayGoals'); };
    client.sendNotification("vscoq/stepForward", {textDocument: textDocument});
};

export const sendStepBackward = (editor: TextEditor,  client: Client) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    const textDocument = VersionedTextDocumentIdentifier.create(uri.toString(), version);
    if(!GoalPanel.currentPanel) {commands.executeCommand('vscoq.displayGoals'); };
    client.sendNotification("vscoq/stepBackward", {textDocument: textDocument});
};

