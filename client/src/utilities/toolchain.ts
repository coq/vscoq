import { window, workspace } from 'vscode';
import { Disposable } from "vscode-languageclient";
import { ExecException, exec } from 'child_process';
import * as path from 'path';
import { isFileInFolder } from './fileHelper';
import { ServerSessionOptions } from 'http2';
import { ServerOptions } from 'vscode-languageclient/node';

interface ToolchainResponse {
    status: number; 
    errorMessage?: string; 
}

export default class VsCoqToolchainManager implements Disposable {
    
    private static _channel: any = window.createOutputChannel('vscoq-toolchain-manager');
    private _vscoqtopPath: string = ""; 

    public dispose(): void {
        
    }



    public intialize() : Promise<ToolchainResponse> {
        VsCoqToolchainManager._channel.appendLine("SEARCHING");
        return new Promise((resolve, reject) => {
            this.vscoqtopPath().then(vscoqtopPath => {
                if(vscoqtopPath) {
                    VsCoqToolchainManager._channel.appendLine("Found path: " + vscoqtopPath);
                    this._vscoqtopPath = vscoqtopPath;
                    this.findCoq().then(
                        res => {
                            resolve({
                                status: 0
                            });
                        }, 
                        err => {
                            reject(err);
                        }
                    );

                } else {
                    VsCoqToolchainManager._channel.appendLine("Did not find path");
                    reject({
                        status: 1, 
                        errorMessage: "Could not find vscoqtop"
                    });
                }
            })
        });
        
    };

    public getServerConfiguration() : ServerOptions {

        const config = workspace.getConfiguration('vscoq');
        const serverOptions : ServerOptions = {
            command: this._vscoqtopPath, 
            args: config.args
        };
        return serverOptions;
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
            return vscoqtopPath; 
        }
        else {
            return await this.searchForVscoqtopInPath();
        }
    }

    private async searchForVscoqtopInPath () : Promise<string> {
        const pathVars = this.splitEnvPath(this.getEnvPath());
        for(let i in pathVars) {
            VsCoqToolchainManager._channel.appendLine(pathVars[i]);
            if(await isFileInFolder('vscoqtop', pathVars[i])) {
                return pathVars[i] + '/vscoqtop';
            }
        }
        return "";
    }

    //Check if vscoqtop can load the prelude at its expected installation site, 
    //or wherever the user specified by passing -coqlib. 
    //(since 8.18 -where does not only print where the prelude is expected to be, 
    //but also checks it exists).
    private findCoq() : Promise<ToolchainResponse> {
        
        const config = workspace.getConfiguration('vscoq').get('args') as string[];
        const options = ["-where"].concat(config);
        const cmd = [this._vscoqtopPath].concat(options).join(' ');

        return new Promise((resolve, reject) => {
            exec(cmd, (error, stdout, stderr) => {

                if(error) {
                    reject({
                        status: 2, 
                        errorMessage: `${this._vscoqtopPath} cannot run properly since the installation of coq standard library seems broken: ${stderr}\n
                        If this is not the coq installation you wish to use , set the right path in the settings panel.`
                    });
                } else {
                    resolve({
                        status: 0
                    });
                }
                
            });
        });
    };

}