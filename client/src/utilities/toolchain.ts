import { window, workspace } from 'vscode';
import { Disposable } from "vscode-languageclient";
import { exec } from 'child_process';
import * as path from 'path';

export default class VsCoqToolchainManager implements Disposable {
    
    private static _channel: any = window.createOutputChannel('vscoq-toolchain-manager');

    public dispose(): void {
        
    }
    
    public performChecks() : void {
        const vscoqtopPath = this.vscoqtopPath();
        if(vscoqtopPath) {
            VsCoqToolchainManager._channel.appendLine("Found vscoqtop, searching for coq libs");
            this.checkIfCoqFound(vscoqtopPath);
        } else {
            VsCoqToolchainManager._channel.appendLine("Could not find vscoqtop, notiftying user");
            window.showErrorMessage("Could not find vscoqtop, please provide a path in user settings");
        }
    };

    private getEnvPath() : string {
        if(process.platform === 'win32') {
            return process.env.Path ?? '';
        } else {
            return process.env.PATH ?? '';
        }
    }

    private setEnvPath(value: string) {
        if(process.platform === 'win32') {
            process.env.Path = value;
        } else {
            process.env.PATH = value;
        }
    }

    private splitEnvPath(value: string) : string[] {
        return value.split(path.delimiter);
    }

    private joinEnvPath(value: string[]) : string {
        return value.join(path.delimiter);
    }

    private vscoqtopPath () : string {
        const path = workspace.getConfiguration('vscoq').get('path') as string;
        if(path) {
            VsCoqToolchainManager._channel.appendLine("Found vscoqtop in user configuration: " + path);
            return path; 
        }
        else {
            VsCoqToolchainManager._channel.appendLine("No path set for vscoqtop in user configuration, querying PATH");
            return this.searchForVscoqtopInPath();
        }

    }

    private searchForVscoqtopInPath () : string {
        const pathVars = this.splitEnvPath(this.getEnvPath());
        VsCoqToolchainManager._channel.appendLine('Searching Path var: ');
        for(let i in pathVars) {
            if(path.basename(pathVars[i]) === 'vscoqtop') {
                VsCoqToolchainManager._channel.appendLine("Found vscoqtop in PATH: " + pathVars[i]);
                return pathVars[i];
            }
        }
        return "";
    }

    private checkIfCoqFound(vscoqtopPath: string) {
        const cmd = vscoqtopPath + " -where";
        VsCoqToolchainManager._channel.appendLine("Launching command: " + cmd );
        exec(cmd, (error, stdout, stderr) => {
            if(error) {
                VsCoqToolchainManager._channel.appendLine(error);
                window.showErrorMessage(stderr);
            } else {
                VsCoqToolchainManager._channel.appendLine(stdout);
                VsCoqToolchainManager._channel.appendLine(stderr);
            }
        });
    };

}