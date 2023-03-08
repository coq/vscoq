import { window } from 'vscode';
import { Disposable } from "vscode-languageclient";
import * as path from 'path';

export default class CoqToolchainManager implements Disposable {
    
    private static _channel: any = window.createOutputChannel('vscoq-toolchain-manager');

    public dispose(): void {
        
    }

    public findCoqToolchainBin() {
        this.searchForCoqInPath();
    }

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

    private searchForCoqInPath () {
        const pathVars = this.splitEnvPath(this.getEnvPath());
        CoqToolchainManager._channel.appendLine('Searching Path var: ');
        for(let i in pathVars) {
            CoqToolchainManager._channel.appendLine(pathVars[i]);
        }
    }
}