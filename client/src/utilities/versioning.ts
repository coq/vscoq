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
            client.writeToChannel("Intialized server " + name + " [" + version + "]");
            if(!checkCompat(extensionVersion, version)) {
                window.showErrorMessage(name + ' ' + version + ' and vscoq ' + extensionVersion + ' are not compatible.'); 
            }
        } else {
            client.writeToChannel("Could not run compatibility tests: failed to get serverInfo");
        }  
    } else {
        client.writeToChannel("Could not run compatibility tests: failed to recieve initializeResult");
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