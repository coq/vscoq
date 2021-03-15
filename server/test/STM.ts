// The module 'assert' provides assertion methods from node
import * as assert from 'assert';
import * as vscode from 'vscode-languageserver';
import * as vscrpc from 'vscode-jsonrpc';
import * as semver from 'semver';

import {CoqStateMachine, StateMachineCallbacks} from '../src/stm/STM';
import {Settings, CoqSettings, CoqTopSettings} from '../src/protocol';
import * as coqtop from '../src/coqtop/CoqTop';

function getText(text: string, range?: vscode.Range) : string {
  const lines = text.split(/\r\n|\n\r|\n/);
  const newLines = text.split(/[^\r\n]+/);
  newLines.shift();
  const lineAt = (l: number) => lines[l] + newLines[l];

  if(range.start.line === range.end.line)
    return lineAt(range.start.line).substring(range.start.character, range.end.character);
  else
    return lineAt(range.start.line).substring(range.start.character) +
      lines.slice(range.start.line+1, range.end.line).map((l,idx) => l + newLines[idx + range.start.line+1]).join('') +
      lineAt(range.end.line).substring(0, range.end.character);
}

class MockCoqTop extends coqtop.CoqTop {
  currentState = 0;
  dispose() {};
  isRunning() { return true; };
  getVersion() { return semver.coerce("mock-version") };
  async startCoq() { return {stateId: 0} };
  isConnected() { return true };
  async coqInterrupt() { return true };
  async coqInit () { return {stateId: 0} };
  async coqQuit () {};
  async coqGoal () : Promise<{ mode: 'no-proof' }> { return {mode: 'no-proof'} };
  async getStatus(force: boolean) { return {path: [], allProofs: [], proofNumber: 0} };
  async coqAddCommand(command: string, editId: number, stateId: number, verbose?: boolean) { return {stateId: ++this.currentState, message: ""} };
  async coqEditAt(stateId: number) { return {} };
  async coqLtacProfilingResults(stateId?: number, routeId?: number) {};
  async coqResizeWindow(columns: number) {};
  async coqQuery(query: string, stateId?: number, routeId?: number) { return; };
  async coqGetOptions(options) {};
  async coqSetOptions(options) {};
}

describe("CoqStateMachine", function() {
  const projectSettings : Settings = {
    coq: {
      autoRevealProofStateAtCursor: false,
      externalViewScheme: "file",
      externalViewUrlCommand: "",
      loadCoqProject: false,
      coqProjectRoot: ".",
      interpretToEndOfSentence: false,
      moveCursorToFocus: false,
      format: {
        enable: false,
        indentAfterBullet: "none",
        indentAfterOpenProof: false,
        unindentOnCloseProof: false,
      },
    } as CoqSettings,
    coqtop: {
      args: [],
      binPath: "",
    } as CoqTopSettings,
  };
  const project = {
    console: {
      ...console,
      attach: undefined,
      connection: undefined,
      fillServerCapabilities: undefined,
      initialize() {}
    },
    getCoqProjectRoot: () => ".",
    settings: projectSettings,
  };

  const stmCallbacks : StateMachineCallbacks = {
    sentenceStatusUpdate() : void {},
    clearSentence() : void {},
    updateStmFocus(): void {},
    error() : void {},
    message() : void {},
    ltacProfResults() : void {},
    coqDied() : void {},
  }


  function makeChange(docText: string, startLine: number, startCharacter: number, endLine: number, endCharacter: number, text: string) : vscode.TextDocumentContentChangeEvent {
    const range = vscode.Range.create(startLine, startCharacter, endLine, endCharacter);
    return {
      range: range,
      text: text,
      rangeLength: getText(docText, range).length,
    }
  }

  function range(a,b,c,d) {
    return vscode.Range.create(a,b,c,d);
  }

  function pos(a,b) {
    return vscode.Position.create(a,b);
  }

  let cancellation : vscrpc.CancellationTokenSource;
  beforeEach(function() {
    cancellation = new vscrpc.CancellationTokenSource();
  })

  describe('applyChangesToDocumentText', function() {
    it('STM.applyChangesToDocumentText', async function() {
      const commands = [{text: "Goal True.", range: range(0,0,0,10)},{text: "\npose True.", range: range(0,10,1,10)}];
      // const project = new CoqProject("", )
      let stm = new CoqStateMachine(project, () => new MockCoqTop(), stmCallbacks);
      assert.equal(stm.getStatesText(), "");
      await stm.interpretToPoint(pos(2,0), function*() { yield *commands; }, false, false, cancellation.token);
      assert.equal(stm.getStatesText(), "Goal True.\npose True.");
      stm.applyChanges([makeChange("Goal True.\npose True.\n", 0, 10, 1, 10, "")], 1, "Goal True.\n")
      assert.equal(stm.getStatesText(), "Goal True.");
      stm.applyChanges([makeChange("Goal True.\n", 0, 0, 0, 0, "pose True.\n")], 2, "pose True.\nGoal True.\n")
      assert.equal(stm.getStatesText(), "");
      await stm.flushEdits();
      assert.ok(!stm.isBusy(), "STM should not be busy")
      assert.ok(stm.assertSentenceConsistency(), "Sentence states are inconsistent");
    })
  })

});
