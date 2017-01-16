// The module 'assert' provides assertion methods from node
import * as assert from 'assert';
import * as diff from 'diff';
import * as os from 'os';
import * as process from 'process';
import * as path from 'path';
import * as fs from 'fs';
import * as util from 'util';

import * as async from '../src/util/nodejs-async';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as text from '../src/util/AnnotatedText';
import * as coqProto from '../src/coqtop/coq-proto';
import {CoqTop as CoqTop8} from '../src/coqtop/CoqTop8';
import * as coqtop from '../src/coqtop/CoqTop';
import * as proto from '../src/protocol';

const COQBIN_8_5 = process.env.COQBIN_8_5 || 'C:/Coq8.5lp/bin';

class TraceConsole {
  public state = {
    log: new Array<string>(),
    warn: new Array<string>(),
    error: new Array<string>(),
    info: new Array<string>(),
  };
  public log(s: string) { this.state.log.push(s); }
  public warn(s: string) { this.state.warn.push(s); }
  public error(s: string) { this.state.error.push(s); }
  public info(s: string) { this.state.info.push(s); }
}

function coqtopBin() {
  return path.join(COQBIN_8_5, '/coqtop')
}

// Defines a Mocha test suite to group tests of similar kind together
describe("Coqtop 8.5", function() {
  before("check if coqtop exists", function() {
    if(!fs.existsSync(path.join(COQBIN_8_5, '/coqtop')) && (os.platform()!=='win32' || !fs.existsSync(path.join(COQBIN_8_5, '/coqtop.exe')))) {
      console.warn("Cannot find coqtop: " + coqtopBin());
      console.warn("Please make sure you have set env-var COQBIN_8_5 to point to the binaries directory of Coq 8.5.");
      this.skip();
    }
  })

  it("version", async function() {
    const version = await coqtop.detectVersion(coqtopBin(), "./", dummyConsole);
    assert(version.startsWith("8.5"), "Coqtop does not appear to be version 8.5.\nPlease make sure you have set env-var COQBIN_8_5 to point to the binaries directory of Coq 8.5.")
    const knownVersions = ["8.5", "8.5pl1", "8.5pl2", "8.5pl3"];
    const isKnownVersion = knownVersions.some((v) => v === version);
    if(!isKnownVersion)
      console.warn("Detected version of coqtop is not one of: " + knownVersions.join(', '));
  })

  const settings : proto.CoqTopSettings = {
    binPath: COQBIN_8_5,
    autoUseWrapper: false,
    wrapper: "",
    args: [],
    traceXmlProtocol: false,    
  }

  let dummyConsole = {
    log: (s) => {},
    info: (s) => {},
    warn: (s) => {},
    error: (s) => {},
  }
  let coq : coqtop.CoqTop;
  let feedback: coqProto.StateFeedback[];
  let messages: coqProto.Message[];
  let isClosed: boolean;

  describe("Initialization", function() {
    this.timeout(5000);
    beforeEach("setup coqtop", function() {
      feedback = [];
      messages = [];
      isClosed = false;
      coq = new CoqTop8(settings, "test.v", "./", dummyConsole, {
        onFeedback: (x1) => feedback.push(x1),
        onMessage: (x1) => messages.push(x1),
        onClosed: (error?: string) => isClosed = true,
      });
    })

    it("Init & Quit", async function() {
      const result = await coq.startCoq();
      assert.equal(result.stateId, 1);
      await coq.coqQuit();
      var x = 5;
    })

  })

  describe("Commands", function() {
    let rootState : number;
    this.timeout(4000)

    beforeEach("setup coqtop", async function() {
      feedback = [];
      messages = [];
      isClosed = false;
      coq = new CoqTop8(settings, "test.v", "./", dummyConsole, {
        onFeedback: (x1) => feedback.push(x1),
        onMessage: (x1) => messages.push(x1),
        onClosed: (error?: string) => isClosed = true,
      });
      rootState = (await coq.startCoq()).stateId;
    })

    afterEach("quit coqtop", async function() {
      await coq.coqQuit();
    })

    function sleep(ms) {
      return new Promise(resolve => setTimeout(resolve, ms));
    }
    
    it("Add", async function() {
      let currentState = rootState;
      const result = await coq.coqAddCommand("Check nat.", 1, currentState, true);
      currentState = result.stateId;
      assert.equal(currentState, 2);
    })

    it("Add 'Check', Goal", async function() {
      let currentState = rootState;
      const result = await coq.coqAddCommand("Check nat.", 1, currentState, true);
      currentState = result.stateId;
      assert.equal(currentState, 2);
      const goals = await coq.coqGoal();
      assert.equal(goals.mode, "no-proof");
      const notice = messages.find((x) => x.level === coqProto.MessageLevel.Notice);
      assert.deepStrictEqual(notice, {
        level: coqProto.MessageLevel.Notice,
        message: 'nat\n     : Set',
      })
    })

  })


});