import {
    TextEditor,
} from 'vscode';

import {
    VersionedTextDocumentIdentifier,
} from 'vscode-languageclient/node';

import Client from './client';

export const sendInterpretToPoint = (editor: TextEditor,  client: Client) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    const textDocument = VersionedTextDocumentIdentifier.create(uri.toString(), version);
    const position = editor.selection.active;
    client.sendNotification("vscoq/interpretToPoint", {textDocument: textDocument, position: position});
};

export const sendInterpretToEnd = (editor: TextEditor,  client: Client) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    const textDocument = VersionedTextDocumentIdentifier.create(uri.toString(), version);
    client.sendNotification("vscoq/interpretToEnd", {textDocument: textDocument});
};

export const sendStepForward = (editor: TextEditor,  client: Client) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    const textDocument = VersionedTextDocumentIdentifier.create(uri.toString(), version);
    client.sendNotification("vscoq/stepForward", {textDocument: textDocument});
};

export const sendStepBackward = (editor: TextEditor,  client: Client) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    const textDocument = VersionedTextDocumentIdentifier.create(uri.toString(), version);
    client.sendNotification("vscoq/stepBackward", {textDocument: textDocument});
};

