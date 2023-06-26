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
import { makeVersionedDocumentId } from './utilities/utils';

export const sendInterpretToPoint = (editor: TextEditor,  client: Client) => {
    const textDocument = makeVersionedDocumentId(editor);
    const position = editor.selection.active;
    client.sendNotification("vscoq/interpretToPoint", {textDocument: textDocument, position: position});
};

export const sendInterpretToEnd = (editor: TextEditor,  client: Client) => {
    const textDocument = makeVersionedDocumentId(editor);
    client.sendNotification("vscoq/interpretToEnd", {textDocument: textDocument});
};

export const sendStepForward = (editor: TextEditor,  client: Client) => {
    const textDocument = makeVersionedDocumentId(editor);
    client.sendNotification("vscoq/stepForward", {textDocument: textDocument});
};

export const sendStepBackward = (editor: TextEditor,  client: Client) => {
    const textDocument = makeVersionedDocumentId(editor);
    client.sendNotification("vscoq/stepBackward", {textDocument: textDocument});
};

