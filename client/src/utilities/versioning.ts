import { window, ExtensionContext } from "vscode";
import Client from "../client";


const compatibilityMap = new Map<string, string[]>([
    ['2.0.0', ['1.0.0']]
]);

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

const checkCompat = (clientVersion: string, serverVersion: string|undefined) => {
    const compatibleVersions = compatibilityMap.get(clientVersion);
    if(compatibleVersions !== undefined && serverVersion !== undefined) {
        return (compatibleVersions.includes(serverVersion));
    }
    return false;
};