import { TextEditor, TextEditorSelectionChangeEvent, TextEditorSelectionChangeKind, workspace } from "vscode";
import {
    VersionedTextDocumentIdentifier,
} from 'vscode-languageclient/node';

import { InterpretToPointRequest, UpdateProofViewRequest } from '../protocol/types';

export const makeVersionedDocumentId = (editor: TextEditor) => {
    const uri = editor.document.uri; 
    const version = editor.document.version; 
    return VersionedTextDocumentIdentifier.create(uri.toString(), version);
};

export const makeInterpretToPointRequestParams = (editor: TextEditor) => {
    const textDocument = makeVersionedDocumentId(editor);
    const position = editor.selection.active;
    const params: InterpretToPointRequest = {textDocument, position};
    return params;
};

export const makeExecutionUpdateProofViewRequestParams = (editor: TextEditor) => {
    const textDocument = makeVersionedDocumentId(editor);
    const position = null; 
    return {textDocument, position} as UpdateProofViewRequest;
};

const isMouseOrKeyboardEvent = (evt: TextEditorSelectionChangeEvent) => {
    return evt.kind === TextEditorSelectionChangeKind.Mouse || evt.kind === TextEditorSelectionChangeKind.Keyboard;
}

export const makeCursorPositionUpdateProofViewRequestParams = (evt: TextEditorSelectionChangeEvent) => {

    if (evt.textEditor.document.languageId === "coq" 
        && workspace.getConfiguration('vscoq.proof').mode === 1
        && isMouseOrKeyboardEvent(evt)) 
    {
        const textDocument = makeVersionedDocumentId(evt.textEditor); 
        const position = evt.textEditor.selection.active;
        return {textDocument, position} as UpdateProofViewRequest;
    }

    return null;

};

