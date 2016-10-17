/** Manages the status bar at the bottom of vscode. All Coq documents should go through this module
 * 
 */
import * as vscode from 'vscode';
import * as proto from './protocol';
import * as textUtil from './text-util';

type ReadyState = { status: "ready" };
type ComputingState = { status: "computing",  message: string, startTime: number, computeTimeMS: number, computeStatus: proto.ComputingStatus };
type MessageState = { status: "message", message: string };

type State = ReadyState | ComputingState | MessageState;

class CoqStatusBarManager implements vscode.Disposable {
  private statusBar: vscode.StatusBarItem;
  private computingStatusBar: vscode.StatusBarItem;
  private interruptButtonStatusBar: vscode.StatusBarItem;

  constructor() {
    this.statusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 3);
    this.statusBar.text = 'Loading Coq';
    this.statusBar.show();
    this.computingStatusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 2);
    this.computingStatusBar.tooltip = 'Time elapsed on the current computation';
    this.computingStatusBar.text = '';
    this.interruptButtonStatusBar = vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left, 1);
    this.interruptButtonStatusBar.tooltip = 'Interrupt Coq computation';
    this.interruptButtonStatusBar.color = 'rgba(255,100,100,1)';
    this.interruptButtonStatusBar.command = 'extension.coq.interrupt';
    this.interruptButtonStatusBar.text = '$(primitive-square)';
  }

  public dispose() {
    this.interruptButtonStatusBar.dispose();
    this.computingStatusBar.dispose();
    this.statusBar.dispose();
  }

  public showState(state: State) {
    this.statusBar.show();
    switch(state.status) {
      case "ready": {
        this.statusBar.text = 'Ready';
        this.interruptButtonStatusBar.hide();
        this.computingStatusBar.hide();
        break;
      }
      case "message": {
        const state_ = <MessageState>state;
        this.computingStatusBar.hide();
        this.interruptButtonStatusBar.hide();
        this.statusBar.text = state_.message;
        break;
      }
      case "computing": {
        const state_ = <ComputingState>state;
        this.statusBar.text = state_.message;
        switch(state_.computeStatus) {
          case proto.ComputingStatus.Finished:
            this.computingStatusBar.hide();
            this.interruptButtonStatusBar.hide();
            break;
          case proto.ComputingStatus.Computing:
            if(state_.computeTimeMS > 2000) {
              this.computingStatusBar.text = `[${textUtil.formatTimeSpanMS(state_.computeTimeMS)}]`;
              this.computingStatusBar.show();
              this.interruptButtonStatusBar.show();
            }
            break;
          case proto.ComputingStatus.Interrupted:
            this.computingStatusBar.text = `[Interrupted $(watch) ${textUtil.formatTimeSpanMS(state_.computeTimeMS)}]`;
            this.computingStatusBar.show();
            this.interruptButtonStatusBar.hide();
            break;
        }
        break;
      }
    }
  }

  public hide() {
    this.computingStatusBar.hide();
    this.interruptButtonStatusBar.hide();
    this.statusBar.hide();
  }
}


export class StatusBar implements vscode.Disposable {
  private static manager : CoqStatusBarManager = null;
  private static managerReferenceCount = 0;
  private static focusedContext : StatusBar = null;

  private state: State = { status: "ready" };
  private hidden = false;

  constructor() {
    if(StatusBar.manager == null)
      StatusBar.manager = new CoqStatusBarManager();
    ++StatusBar.managerReferenceCount;
  }

  public dispose() {
    --StatusBar.managerReferenceCount;
    if(StatusBar.managerReferenceCount == 0) {
      StatusBar.manager.hide();
      StatusBar.manager.dispose();
      StatusBar.manager = null;
    }
  }

  public focus() {
    if(StatusBar.focusedContext !== this) {
      StatusBar.focusedContext = this;
      this.refreshState();
    }    
  }

  public unfocus() {
    if(StatusBar.focusedContext == this) {
      StatusBar.focusedContext = null;
      StatusBar.manager.hide();
    }
  }

  private currentMessage() : string {
    if(this.state.status === "message" || this.state.status === "computing")
      return (<MessageState|ComputingState>this.state).message;
    else
      return ""
  }

  public setStateComputing(computeStatus: proto.ComputingStatus, computeTimeMS?: number, message?: string) {
    this.state =
      { status: 'computing'
      , message: message!==undefined ? message : this.currentMessage() 
      , startTime: 0
      , computeTimeMS: computeTimeMS == null ? 0 : computeTimeMS
      , computeStatus: computeStatus };
    this.refreshState();
  }

  public setStateReady() {
    this.state = { status: 'ready' };
    this.refreshState();
  }

  public setStateWorking(name: string) {
    this.state = { status: 'message', message: name };
    this.refreshState();
  }

  private refreshState() {
    if(StatusBar.focusedContext == this && !this.hidden)
      StatusBar.manager.showState(this.state);
  }

  public show() {
    this.hidden = false;
    this.refreshState();
  }

  public hide() {
    if(!this.hidden) {
      this.hidden = true;
      if(StatusBar.focusedContext == this)
        StatusBar.manager.hide();
    }
  }
}




