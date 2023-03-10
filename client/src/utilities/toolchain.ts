import { window, workspace } from 'vscode';
import { Disposable } from "vscode-languageclient";
import { exec } from 'child_process';
import * as path from 'path';
import { isFileInFolder } from './fileHelper';

export default class VsCoqToolchainManager implements Disposable {
    
    private static _channel: any = window.createOutputChannel('vscoq-toolchain-manager');

    public dispose(): void {
        
    }
    
    public performChecks() : void {

        this.vscoqtopPath().then(vscoqtopPath => {
            if(vscoqtopPath) {
                VsCoqToolchainManager._channel.appendLine("Found vscoqtop, searching for coq libs");
                this.checkIfCoqFound(vscoqtopPath);
            } else {
                VsCoqToolchainManager._channel.appendLine("Could not find vscoqtop, notiftying user");
                window.showErrorMessage("Could not find vscoqtop, please provide a path in user settings");
            }
        });

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

    private async vscoqtopPath () : Promise<string> {
        const vscoqtopPath = workspace.getConfiguration('vscoq').get('path') as string;
        if(vscoqtopPath) {
            VsCoqToolchainManager._channel.appendLine("Found vscoqtop in user configuration: " + vscoqtopPath);
            return path.dirname(vscoqtopPath); 
        }
        else {
            VsCoqToolchainManager._channel.appendLine("No path set for vscoqtop in user configuration, querying PATH");
            return await this.searchForVscoqtopInPath();
        }

    }

    private async searchForVscoqtopInPath () : Promise<string> {
        const pathVars = this.splitEnvPath(this.getEnvPath());
        for(let i in pathVars) {
            if(await isFileInFolder('vscoqtop', pathVars[i])) {
                return pathVars[i];
            }
        }
        return "";
    }

    private checkIfCoqFound(vscoqtopPath: string) {
        const options = workspace.getConfiguration('vscoq').get('args') as string[];

        const cmd = ["./vscoqtop -where"].concat(options).join(' ');
        VsCoqToolchainManager._channel.appendLine("Launching command: " + cmd + " in folder: " + vscoqtopPath);
        exec(cmd, {cwd: vscoqtopPath}, (error, stdout, stderr) => {
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