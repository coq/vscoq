// The module 'assert' provides assertion methods from node
import * as assert from 'assert';
import * as diff from 'diff';
import * as os from 'os';
import * as process from 'process';
import * as path from 'path';
import * as fs from 'fs';
import * as util from 'util';
import * as vscode from 'vscode-languageserver';

import * as parser from '../src/parsing/coq-parser';
import * as ast from '../src/parsing/ast-types';


describe.only("coq-parser", function() {

  it('parseSentenceLength', function() {
    assert.equal(parser.parseSentenceLength('Inductive w(k:E):=(). ('), 21);
  })

  it('sentenceLength - SAny', function() {
    assert.deepStrictEqual(parser.parseSentence('Inductive w(k:E):=(). ('), {type: 'any', text: 'Inductive w(k:E):=().', rest: ' ('});
  })

  it('sentenceLength - SInductive', function() {
    assert.deepStrictEqual(parser.parseSentence('Inductive w := a. ('), {type: 'inductive', kind: "Inductive", bodies: [], text: 'Inductive w := a.', rest: ' ('});
  })

});