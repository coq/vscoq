import { window, ExtensionContext } from "vscode";
import { compareVersions } from "compare-versions";
import Client from "../client";


export const checkVersion = (client: Client, context: ExtensionContext) => {
    const extensionVersion = context.extension.packageJSON.version;
    const initializeResult = client.initializeResult;
    if(initializeResult !== undefined) {
        const serverInfo =client.initializeResult?.serverInfo;
        if(serverInfo !== undefined) {
            const {name, version} = serverInfo;
            Client.writeToVscoq2Channel("[Versioning] Intialized server " + name + " [" + version + "]");
            if(extensionVersion !== version) {
                window.showErrorMessage('This version of VsCoq requires version ' + extensionVersion + ' of ' + name);
            }
        } else {
            Client.writeToVscoq2Channel("Could not run compatibility tests: failed to get serverInfo");
        }  
    } else {
        Client.writeToVscoq2Channel("Could not run compatibility tests: failed to recieve initializeResult");
    }

};

//We will add version ranges as we start releasing
const checkCompat = (clientVersion: string, serverVersion: string|undefined) => {
    if(serverVersion !== undefined) {
        if(compareVersions(clientVersion, '1.0.0') >= 1) {
            return compareVersions(serverVersion, '1.0.0') >= 1;
        }
    }
    return false;
};