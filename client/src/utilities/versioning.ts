import { window, ExtensionContext } from "vscode";
import { compareVersions } from "compare-versions";
import Client from "../client";

export const getCoqdocUrl = (coqVersion: string) => {
    if(compareVersions(coqVersion, "8.18.0") >= 0 && compareVersions(coqVersion, "9.0.0") < 0) {
        return (`https://coq.inria.fr/doc/V${coqVersion}/refman/index.html`);
    }
    return "https://coq.inria.fr/doc/master/refman/index.html"
};

export const checkVersion = (client: Client, context: ExtensionContext) => {
    const extensionVersion = context.extension.packageJSON.version;
    const initializeResult = client.initializeResult;
    if(initializeResult !== undefined) {
        const serverInfo = client.initializeResult?.serverInfo;
        if(serverInfo !== undefined) {
            const {name, version} = serverInfo;
            Client.writeToVscoq2Channel("[Versioning] Intialized server " + name + " [" + version + "]");
            if(!checkCompat(extensionVersion, version)) {
                window.showErrorMessage('This version of VsCoq requires version ' + versionRequirements[extensionVersion] + ' of ' + name + '. Found version: ' + version + '. Please upgrade the language server.');
            }
        } else {
            Client.writeToVscoq2Channel("Could not run compatibility tests: failed to get serverInfo");
        }  
    } else {
        Client.writeToVscoq2Channel("Could not run compatibility tests: failed to receive initializeResult");
    }

};

type VersionReq = {
    [index: string]: string
};

/*  Version requirements for the client. Syntax is client version : minimum server version */
const versionRequirements : VersionReq = {
    '2.0.0': '2.0.0', 
    '2.0.1': '2.0.0', 
    '2.0.2': '2.0.0', 
    '2.0.3': '2.0.3',
    '2.1.0': '2.0.3',
    '2.1.1': '2.1.1',
    '2.1.2': '2.1.2',
    '2.1.3': '2.1.3',
    '2.1.5': '2.1.5',
    '2.1.6': '2.1.5',
    '2.1.7': '2.1.7',
    '2.2.0': '2.1.7',
    '2.2.1': '2.2.1',
    '2.2.2': '2.2.2',
    '2.2.3': '2.2.2',
    '2.2.4': '2.2.4'
};

//We will add version ranges as we start releasing
const checkCompat = (clientVersion: string, serverVersion: string|undefined) => {
    if(serverVersion !== undefined) {
        return compareVersions(serverVersion, versionRequirements[clientVersion]) >= 0;
    }
    return false;
};