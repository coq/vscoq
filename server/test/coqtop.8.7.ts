// The module 'assert' provides assertion methods from node
import * as assert from 'assert';
import * as os from 'os';
import * as process from 'process';
import * as path from 'path';
import * as fs from 'fs';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as text from '../src/util/AnnotatedText';
import * as coqProto from '../src/coqtop/coq-proto';
import {CoqTop as CoqTop8} from '../src/coqtop/CoqTop8';
import * as coqtop from '../src/coqtop/CoqTop';
import * as proto from '../src/protocol';
import { RemoteConsole } from 'vscode-languageserver';

const COQBIN_8_6 = process.env.COQBIN_8_6 || 'C:/Coq_trunk_build/bin';

function coqtopBin() {
  return path.join(COQBIN_8_6, '/coqtop')
}

// Defines a Mocha test suite to group tests of similar kind together
describe("Coqtop 8.6", function() {
  before("check if coqtop exists", function() {
    if(!fs.existsSync(path.join(COQBIN_8_6, '/coqtop')) && (os.platform()!=='win32' || !fs.existsSync(path.join(COQBIN_8_6, '/coqtop.exe')))) {
      console.warn("Cannot find coqtop: " + coqtopBin());
      console.warn("Please make sure you have set env-var COQBIN_8_6 to point to the binaries directory of Coq 8.6.");
      this.skip();
    }
  })

  it("version", async function() {
    const version = await coqtop.detectVersion(coqtopBin(), "./", dummyConsole);
    assert(version.startsWith("8.6"), "Coqtop does not appear to be version 8.5.\nPlease make sure you have set env-var COQBIN_8_5 to point to the binaries directory of Coq 8.5.")
    const knownVersions = ["8.6.0"];
    const isKnownVersion = knownVersions.some((v) => v === version);
    if(!isKnownVersion)
      console.warn("Detected version of coqtop is not one of: " + knownVersions.join(', '));
  })

  const settings : proto.CoqTopSettings = {
    binPath: COQBIN_8_6,
    coqtopExe: "coqtop",
    coqidetopExe: "coqidetop.opt",
    args: [],
    startOn: "open-script",
    dunePath: "",
    useDune: false
  }

  let dummyConsole: RemoteConsole = {
    log: () => {},
    info: () => {},
    warn: () => {},
    error: () => {},
    attach: () => {},
    initialize: () => {},
    fillServerCapabilities: () => {},
    connection: undefined,
  };
  let coq: coqtop.CoqTop;
  let feedback: coqProto.StateFeedback[];
  let messages: coqProto.Message[];

  describe("Initialization", function() {
    this.timeout(5000);
    beforeEach("setup coqtop", function() {
      feedback = [];
      messages = [];
      coq = new CoqTop8(settings, "test.v", "./", dummyConsole);
      coq.onFeedback((x1) => feedback.push(x1));
      coq.onMessage((x1) => messages.push(x1));
    })

    it("Init & Quit", async function() {
      const result = await coq.startCoq();
      assert.equal(result.stateId, 1);
      await coq.coqQuit();
    })

  })

  describe("Commands", function() {
    let rootState : number;

    beforeEach("setup coqtop", async function() {
      feedback = [];
      messages = [];
      coq = new CoqTop8(settings, "test.v", "./", dummyConsole);
      coq.onFeedback((x1) => feedback.push(x1));
      coq.onMessage((x1) => messages.push(x1));
      rootState = (await coq.startCoq()).stateId;
    })

    afterEach("quit coqtop", async function() {
      await coq.coqQuit();
    })

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
      notice.message = text.normalizeText(notice.message);
      assert.deepStrictEqual(notice, {
        level: coqProto.MessageLevel.Notice,
        location: null,
        message: {scope: "_", text:[{scope: "constr.reference", text: 'nat'}, '\n     : ', {scope: "constr.type", text: 'Set'}]},
      })
    })

  })


});
