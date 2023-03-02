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
import { makeInterpretToPointRequestParams, makeVersionedDocumentId } from './utilities/requests';

export const sendInterpretToPoint = (editor: TextEditor,  client: Client) => {
    const req = new RequestType<InterpretToPointRequest, UpdateProofViewResponse, void>("vscoq/interpretToPoint");
    const params = makeInterpretToPointRequestParams(editor);
    client.sendRequest(req, params);
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

