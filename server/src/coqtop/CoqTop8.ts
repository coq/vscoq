'use strict';

import * as net from 'net';
import * as path from 'path';
import * as vscode from 'vscode-languageserver';
import * as semver from 'semver';

import {ChildProcess, spawn} from 'child_process';
import {CoqTopSettings} from '../protocol';

import * as coqtop from './CoqTop';
export {Interrupted, CoqtopSpawnError, CallFailure,
  InitResult, AddResult, EditAtFocusResult, EditAtResult, ProofView,
  NoProofTag, ProofModeTag, NoProofResult, ProofModeResult, GoalResult} from './CoqTop';
import {CoqtopSpawnError, InitResult} from './CoqTop';
import {IdeSlave as IdeSlave8, IdeSlaveState} from './IdeSlave8';
import { AddressInfo } from 'net';

export class CoqTop extends IdeSlave8 implements coqtop.CoqTop {
  private mainChannelServer: net.Server;
  private mainChannelServer2: net.Server;
  private controlChannelServer: net.Server;
  private controlChannelServer2: net.Server;
  private coqtopProc : ChildProcess = null;
  private readyToListen: Thenable<void>[];
  private settings : CoqTopSettings;
  private scriptFile : string;
  private projectRoot: string;
  private coqtopVersion : semver.SemVer;
  private sockets : net.Socket[] = [];

  constructor(settings : CoqTopSettings, scriptFile: string, projectRoot: string, console: vscode.RemoteConsole) {
    super(console);
    this.settings = settings;
    this.scriptFile = scriptFile;
    this.projectRoot = projectRoot;
    this.mainChannelServer = net.createServer();
    this.mainChannelServer2 = net.createServer();
    this.controlChannelServer = net.createServer();
    this.controlChannelServer2 = net.createServer();
    this.mainChannelServer.maxConnections = 1;
    this.mainChannelServer2.maxConnections = 1;
    this.controlChannelServer.maxConnections = 1;
    this.controlChannelServer2.maxConnections = 1;

    this.readyToListen = [
      this.startListening(this.mainChannelServer),
      this.startListening(this.mainChannelServer2),
      this.startListening(this.controlChannelServer),
      this.startListening(this.controlChannelServer2)
    ];

  }

  public /* override */ dispose() {
    if(this.isRunning() && this.callbacks.onClosed) {
      this.callbacks.onClosed(false);
    }

    super.dispose();

    this.sockets.forEach(s => s.destroy());
    this.sockets = [];

    if(this.coqtopProc) {
      try {
        this.coqtopProc.kill();
        if(this.coqtopProc.connected)
          this.coqtopProc.disconnect();
      } catch(e) {}
      this.coqtopProc = null;
    }
    this.coqtopProc = null;
  }

  public isRunning() : boolean {
    return this.coqtopProc != null;
  }

  public async startCoq() : Promise<InitResult> {
    if(this.state !== IdeSlaveState.Disconnected)
      throw new CoqtopSpawnError(this.coqtopBin, "coqtop is already started");

    this.console.log('starting coqtop');

    let coqtopVersion = await coqtop.detectVersion(this.coqtopBin, this.projectRoot, this.console);
    if(coqtopVersion)
      this.console.log(`Detected coqtop version ${coqtopVersion}`)
    else
      this.console.warn(`Could not detect coqtop version`)

    this.coqtopVersion = semver.coerce(coqtopVersion);
    this.console.log(`Coqtop version parsed into semver version ${this.coqtopVersion.format()}`);

    await this.setupCoqTopReadAndWritePorts();

    return await this.coqInit();
  }


  protected async /* override */ checkState() : Promise<void> {
    if(this.coqtopProc === null)
      this.startCoq();
    super.checkState();
  }

  private startListening(server: net.Server) : Promise<void> {
    const port = 0;
    const host = 'localhost';
    return new Promise<void>((resolve,reject) => {
      server.on('error', (err) => reject(err));
      server.listen({port: port, host: host}, () => {
        const serverAddress = server.address() as AddressInfo;
        this.console.log(`Listening at ${serverAddress.address}:${serverAddress.port}`);
        resolve();
      });
    });
  }

  private acceptConnection(server: net.Server, name:string) : Promise<net.Socket> {
    return new Promise<net.Socket>((resolve) => {
      server.once('connection', (socket:net.Socket) => {
        this.sockets.push(socket);
        this.console.log(`Client connected on ${name} (port ${socket.localPort})`);
        // socket.setEncoding('utf8');
        // // if (dataHandler)
        //   socket.on('data', (data:string) => dataHandler(data));
        // socket.on('error', (err:any) => this.onCoqTopError(err.toString() + ` (${name})`));
        resolve(socket);
      });
    });
  }

  public getVersion() {
    return this.coqtopVersion;
  }


  /** Start coqtop.
   * Use two ports: one for reading & one for writing; i.e. HOST:READPORT:WRITEPORT
   */
  private async setupCoqTopReadAndWritePorts() : Promise<void> {
    await Promise.all(this.readyToListen);

    var mainAddr = this.mainChannelServer.address() as AddressInfo;
    var mainPortW = (this.mainChannelServer2.address() as AddressInfo).port;
    var controlAddr = this.controlChannelServer.address() as AddressInfo;
    var controlPortW = (this.controlChannelServer2.address() as AddressInfo).port;
    var mainAddressArg = mainAddr.address + ':' + mainAddr.port + ':' + mainPortW;
    var controlAddressArg = controlAddr.address + ':' + controlAddr.port + ':' + controlPortW;

    try {
      this.startCoqTop(this.spawnCoqTop(mainAddressArg, controlAddressArg));
    } catch(error) {
      this.console.error('Could not spawn coqtop: ' + error);
      throw new CoqtopSpawnError(this.coqtopBin, error);
    }

    let channels = await Promise.all([
        this.acceptConnection(this.mainChannelServer, 'main channel R'), //, 'main channel R', (data) => this.onMainChannelR(data)),
        this.acceptConnection(this.mainChannelServer2, 'main channel W'),
        this.acceptConnection(this.controlChannelServer, 'control channel R'),
        this.acceptConnection(this.controlChannelServer2, 'control channel W'),
      ]);

    this.connect(this.coqtopVersion.format(), channels[0], channels[1], channels[2], channels[3])
  }

  private startCoqTop(process : ChildProcess) {
    this.coqtopProc = process;
    this.console.log(`coqtop started with pid ${this.coqtopProc.pid}`);
    this.coqtopProc.stdout.on('data', (data:string) => this.coqtopOut(data))
    this.coqtopProc.on('exit', (code:number) => {
      this.console.log('coqtop exited with code: ' + code);
      if(this.isRunning() && this.callbacks.onClosed)
        this.callbacks.onClosed(false, 'coqtop closed with code: ' + code);
      this.dispose();
    });
    this.coqtopProc.stderr.on('data', (data:string) => {
      this.console.log('coqtop-stderr: ' + data);
    });
    this.coqtopProc.on('close', (code:number) => {
      this.console.log('coqtop closed with code: ' + code);
      if(this.isRunning() && this.callbacks.onClosed)
        this.callbacks.onClosed(false, 'coqtop closed with code: ' + code);
      this.dispose();
    });
    this.coqtopProc.on('error', (code:number) => {
      this.console.log('coqtop could not be started: ' + code);
      if(this.isRunning() && this.callbacks.onClosed)
        this.callbacks.onClosed(true, 'coqtop closed with code: ' + code);
      this.dispose();
    });
    // this.coqtopProc.stdin.write('\n');
  }

  private coqtopOut(data:string) {
    this.console.log('coqtop-stdout:' + data);
  }

  private get coqtopBin() {
    return path.join(this.settings.binPath.trim(), 'coqtop');
  }

  private get coqidetopBin() {
    return path.join(this.settings.binPath.trim(), 'coqidetop.opt');
  }

  private spawnCoqTop(mainAddr : string, controlAddr: string) {
    var topfile : string[] = [];
    if (semver.satisfies(this.coqtopVersion, ">= 8.10")) {
      topfile = ['-topfile', this.scriptFile];
    }
    if (semver.satisfies(this.coqtopVersion, ">= 8.9")) {
      var coqtopModule = this.coqidetopBin;
      // var coqtopModule = 'cmd';
      var args = [
        // '/D /C', this.coqPath + '/coqtop.exe',
        '-main-channel', mainAddr,
        '-control-channel', controlAddr,
        '-async-proofs', 'on'
        ].concat(this.settings.args).concat(topfile);
    } else {
      var coqtopModule = this.coqtopBin;
      // var coqtopModule = 'cmd';
      var args = [
        // '/D /C', this.coqPath + '/coqtop.exe',
        '-main-channel', mainAddr,
        '-control-channel', controlAddr,
        '-ideslave',
        '-async-proofs', 'on'
        ].concat(this.settings.args);
    }
    this.console.log('exec: ' + coqtopModule + ' ' + args.join(' '));
    return spawn(coqtopModule, args, {detached: false, cwd: this.projectRoot});
  }

  public /* override */ async coqInterrupt() : Promise<boolean> {
    if(!this.coqtopProc)
      return false;
    else {
      this.console.log('--------------------------------');
      this.console.log('Sending SIGINT');
      this.coqtopProc.kill("SIGINT");
      return true;
    }
  }
}
