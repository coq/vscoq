import { window, ExtensionContext } from "vscode";
import { compareVersions } from "compare-versions";
import Client from "../client";


export const checkVersion = (client: Client, context: ExtensionContext) => {
    const extensionVersion = context.extension.packageJSON.version;
    const initializeResult = client.initializeResult;
    if(initializeResult !== undefined) {
        const serverInfo = client.initializeResult?.serverInfo;
        if(serverInfo !== undefined) {
            const {name, version} = serverInfo;
            Client.writeToVscoq2Channel("[Versioning] Intialized server " + name + " [" + version + "]");
            if(!checkCompat(extensionVersion, version)) {
                window.showErrorMessage('This version of VsCoq requires version ' + versionRequirements[extensionVersion] + ' of ' + name + '. Found version: ' + version);
            }
        } else {
            Client.writeToVscoq2Channel("Could not run compatibility tests: failed to get serverInfo");
        }  
    } else {
        Client.writeToVscoq2Channel("Could not run compatibility tests: failed to recieve initializeResult");
    }

};

type VersionReq = {
    [index: string]: string
};

/*  Version requirements for the client. Syntax is client version : minimum server version */
const versionRequirements : VersionReq = {
    '2.0.0': '2.0.0', 
    '2.0.1': '2.0.0', 
    '2.0.2': '2.0.0'
};

//We will add version ranges as we start releasing
const checkCompat = (clientVersion: string, serverVersion: string|undefined) => {
    if(serverVersion !== undefined) {
        return compareVersions(serverVersion, versionRequirements[clientVersion]) >= 0;
    }
    return false;
};