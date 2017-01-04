// The module 'assert' provides assertion methods from node
import * as assert from 'assert';
import * as diff from 'diff';
import * as util from 'util';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as text from '../src/util/AnnotatedText';
import * as perr from '../src/parsing/error-parsing';

// Defines a Mocha test suite to group tests of similar kind together
describe("error-parsing", () => {
  function parse(err: text.AnnotatedText) {
    return {err: err, perr: perr.parseError(err)}
  }

  describe("parseError", function() {
    it("'Imposssible to unify...'", (() => {
      const x0 = parse('Impossible to unify "an expression" with "an expression"');
      assert.equal(x0.err, x0.perr);
      const x1 = parse('Impossible to unify "an expression" with "an Expression"');
      assert.deepStrictEqual(x1.perr, ['Impossible to unify "an ',{diff: "removed", text: "expression"}, '" with "an ',{diff: "added", text: "Expression"}, '"']);
      const x2 = parse('Impossible to unify "an expression" with "an xpression"');
      assert.deepStrictEqual(x2.perr, ['Impossible to unify "an ',{diff: "removed", text: "expression"}, '" with "an ',{diff: "added", text: "xpression"}, '"']);
    }));

    it("'Unable to unify...'", (() => {
      const x3 = parse('Error: Unable to unify "True" with "False".');
      assert.deepStrictEqual(x3.perr, ['Error: Unable to unify "', {diff: "removed", text: "True"}, '" with "', {diff: "added", text: "False"}, '".']);
    }));

    it("'The term has type...'", (() => {
      const x4 = parse('\nError:\nThe term ""a"" has type "string"\nwhile it is expected to have type\n"bool".');
      assert.deepStrictEqual(x4.perr, ['\nError:\nThe term ""a"" has type "', {diff: "removed", text: "string"}, '"\nwhile it is expected to have type\n"', {diff: "added", text: "bool"}, '".']);
    }));

    it("'The file... contains library...'", (() => {
      const x0 = parse('The file ident.vo contains library dirpath and not library dirpath’')
      assert.deepStrictEqual(x0.perr, ['The file ident.vo contains library dirpath and not library dirpath', {diff: "added", text: "’"}]);
      const x1 = parse('The file ident.vo contains library Moo.dirpath and not library Foo.dirpath’')
      assert.deepStrictEqual(x1.perr, ['The file ident.vo contains library ', {diff: "removed", text: "Moo"}, '.dirpath and not library ', {diff: "added", text: "Foo"}, '.dirpath', {diff: "added", text: "’"}]);
    }));

    it("'Found target ...'", (() => {
      const x6 = parse('Error:  Found target  class "foo" instead  of "Foo".')
      assert.deepStrictEqual(x6.perr, ['Error:  Found target  class "', {diff: "removed", text: "foo"}, '" instead  of "', {diff: "added", text: "Foo"}, '".']);
    }));

    it("'Refiner was given an argument...'", (() => {
      const x7 = parse('Error: Refiner was given an argument "asdf234 3 5r ()23 " of type "foo" instead of "fOO".')
      assert.deepStrictEqual(x7.perr, ['Error: Refiner was given an argument "asdf234 3 5r ()23 " of type "', {diff: "removed", text: "foo"}, '" instead of "', {diff: "added", text: "fOO"}, '".']);
    }));

  })
});