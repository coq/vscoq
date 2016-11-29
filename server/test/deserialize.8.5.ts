// The module 'assert' provides assertion methods from node
import * as assert from 'assert';
import * as diff from 'diff';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as text from '../src/util/AnnotatedText';
import * as proto from '../src/coqtop/coq-proto';
import * as db from '../src/coqtop/xml-protocol/deserialize.base';
import * as d from '../src/coqtop/xml-protocol/deserialize.8.5';
import * as p from '../src/coqtop/xml-protocol/coq-xml';
import * as stream from 'stream';

// Defines a Mocha test suite to group tests of similar kind together
suite("Deserialize 8.5", () => {
  let data : stream.PassThrough;
  let deserializer : db.Deserialize;
  let parser : p.XmlStream;

  beforeEach("init", function() {
    data = new stream.PassThrough();
    deserializer = new d.Deserialize_8_5();
    parser = new p.XmlStream(data,deserializer);
  })

  function parse(xml: string|string[]) : Promise<proto.ReturnValue[]> {
    return new Promise<proto.ReturnValue[]>((resolve, reject) => {
      const results : proto.ReturnValue[] = [];
      parser.on('response', (tag, v) => results.push(v));
      parser.on('error', reject);
      parser.on('end', () => resolve(results));
      if(xml instanceof Array)
        xml.forEach((x)=> data.emit('data', x))
      else
        data.emit('data', xml);
      data.emit('end', '')
    })
  }

  test("state_id", async function () {
    const results = await parse('<state_id val="5" />');
    assert.deepStrictEqual(results, [5]);
  });

  test("edit_id", async function () {
    const results = await parse('<edit_id val="6" />');
    assert.deepStrictEqual(results, [6]);
  });

  test("int", async function () {
    const results = await parse('<int>3</int>');
    assert.deepStrictEqual(results, [3]);
  });

  test("string", async function () {
    const results = await parse('<string>hi</string>');
    assert.deepStrictEqual(results, ["hi"]);
  });

  test("string - nbsp gt", async function () {
    const results = await parse('<string>hi&nbsp;there! &gt;:</string>');
    assert.deepStrictEqual(results, ["hi\u00a0there! >:"]);
  });

  test("string: pretty long", async function () {
    const results = await parse('<string>' + ".".repeat(100000) + '</string>');
    assert.deepStrictEqual(results, [".".repeat(100000)]);
  });

  test("unit", async function () {
    const results = await parse('<unit/>');
    assert.deepStrictEqual(results, [{}]);
  });

  test("pair", async function () {
    const results = await parse('<pair><int>4</int><string>hi</string></pair>');
    assert.deepStrictEqual(results, [[4, 'hi']]);
  });

  test("list", async function () {
    const results = await parse('<list><int>4</int><string>hi</string><int>1</int></list>');
    assert.deepStrictEqual(results, [[4, 'hi', 1]]);
  });
  
  test("bool", async function () {
    const results = await parse([
        '<bool val="true"></bool>',
        '<bool val="false"></bool>',
        '<bool val="True"></bool>',
        '<bool val="False"></bool>',
        '<bool val="TruE"></bool>',
        '<bool val="FalsE"></bool>',
      ]);
    assert.deepStrictEqual(results, [true,false,true,false,true,false]);
  });

  test("union", async function () {
    const results = await parse([
      '<union val="in_l"><int>5</int></union>',
      '<union val="in_r"><string>hi</string></union>',
      ]);
    assert.deepStrictEqual(results, [{tag: "inl", value: 5},{tag: "inr", value: "hi"}]);
  });

  test("option", async function () {
    const results = await parse([
      '<option val="some"><int>5</int></option>',
      '<option val="none"/>',
      ]);
    assert.deepStrictEqual(results, [5,null]);
  });

  test("option_value", async function () {
    const results = await parse([
      '<option_value val="intvalue"><option val="some"><int>5</int></option></option_value>',
      '<option_value val="intvalue"><option val="none"/></option_value>',
      '<option_value val="stringoptvalue"><option val="some"><string>hi</string></option></option_value>',
      '<option_value val="stringoptvalue"><option val="none"/></option_value>',
      '<option_value val="boolvalue"><bool val="true"/></option_value>',
      '<option_value val="boolvalue"><bool val="false"/></option_value>',
      '<option_value val="stringvalue"><string>hi</string></option_value>',
      ]);
    assert.deepStrictEqual(results, [5,null,"hi",null,true,false,"hi"]);
  });

  test("option_state", async function () {
    const results = await parse([
      '<option_state><bool val="true"/><bool val="false"/><string>hi</string><int>5</int></option_state>',
      '<option_state><bool val="true"/><bool val="false"/><string>hi</string><string>5</string></option_state>',
      '<option_state><bool val="true"/><bool val="false"/><string>hi</string><bool val="true"/></option_state>',
      ]);
    assert.deepStrictEqual(results, [
      {synchronized: true, deprecated: false, name: "hi", value: 5},
      {synchronized: true, deprecated: false, name: "hi", value: "5"},
      {synchronized: true, deprecated: false, name: "hi", value: true},
    ]);
  });

  test("loc", async function () {
    const results = await parse('<loc start="2" stop="10"/>');
    assert.deepStrictEqual(results, [{start: 2, stop: 10}]);
  });

  test("richpp", async function () {
    const results = await parse('<option val="some"><richpp><_><aa>t</aa>h<bb>er</bb>e</_></richpp></option>');
    assert.notEqual(results, null);
    const r = results.map((r) => text.normalizeText(r as text.AnnotatedText));
    assert.deepStrictEqual(r, [{scope:"_",text:[{scope: "aa", text:"t"},"h",{scope: "bb", text:"er"},"e"]}]);
  });

  test("message_level", async function () {
    const results = await parse([
      '<message_level val="warning"/>',
      '<message_level val="info"/>',
      '<message_level val="notice"/>',
      '<message_level val="error"/>',
      '<message_level val="debug"/>',
      ]);
    assert.deepStrictEqual(results, [
      proto.MessageLevel.Warning, proto.MessageLevel.Info, proto.MessageLevel.Notice,
      proto.MessageLevel.Error, proto.MessageLevel.Debug]);
  });
  
  test("message", async function () {
    const results = await parse([
      '<message><message_level val="warning"/><string>hi</string></message>',
      ]);
    assert.deepStrictEqual(results, [
      {level: proto.MessageLevel.Warning, message: "hi"}]);
  });

  test("feedback - errormsg", async function () {
    const results = await parse('<feedback_content val="errormsg"><loc start="1" stop="3"/><string>hi</string></feedback_content>');
    assert.deepStrictEqual(results, [
      {feedbackKind: "message", level: proto.MessageLevel.Error, location: {start: 1, stop: 3}, message: "hi"}]);
  });

  test("feedback - (sentence-status)", async function () {
    const results = await parse([
      '<feedback_content val="processed"></feedback_content>',
      '<feedback_content val="incomplete"></feedback_content>',
      '<feedback_content val="complete"></feedback_content>',
      '<feedback_content val="processingin"><string>worker</string></feedback_content>',
      ]);
    assert.deepStrictEqual(results[0],{feedbackKind: "sentence-status", status: proto.SentenceStatus.Processed, worker: "", inProgressDelta: 0});
    assert.deepStrictEqual(results[1],{feedbackKind: "sentence-status", status: proto.SentenceStatus.Incomplete, worker: "", inProgressDelta: 0});
    assert.deepStrictEqual(results[2],{feedbackKind: "sentence-status", status: proto.SentenceStatus.Complete, worker: "", inProgressDelta: 0});
    assert.deepStrictEqual(results[3],{feedbackKind: "sentence-status", status: proto.SentenceStatus.ProcessingInWorker, worker: "worker", inProgressDelta: 0});
  });

  suite("LtacProf", () => {
    function ltacprof_tactic(name,total,self,num_calls,max_total,children: string[]) {
      return `<ltacprof_tactic name="${name.toString()}" total="${total.toString()}" self="${self.toString()}" num_calls="${num_calls.toString()}" max_total="${max_total.toString()}">${children.join('')}</ltacprof_tactic>`;
    }

    test("ltacprof_tactic", async function () {
      const results = await parse([
        ltacprof_tactic('abc',0,0,0,0,[]),
        ltacprof_tactic('foo',4.4,3.3,2,1.1,[]),
        ltacprof_tactic('aaa',4.4,3.3,2,1.1,[ltacprof_tactic('bbb',0,0,0,0,[]), ltacprof_tactic('ccc',0,0,0,0,[])]),
        ]);
      assert.deepStrictEqual(results[0],{name: "abc", statistics: {total: 0, local: 0, num_calls: 0, max_total: 0}, tactics: []});
      assert.deepStrictEqual(results[1],{name: "foo", statistics: {total: 4.4, local: 3.3, num_calls: 2, max_total: 1.1}, tactics: []});
      assert.deepStrictEqual(results[2],{
        name: "aaa",
        statistics: {total: 4.4, local: 3.3, num_calls: 2, max_total: 1.1},
        tactics: [
          {name: "bbb", statistics: {total: 0, local: 0, num_calls: 0, max_total: 0}, tactics: []},
          {name: "ccc", statistics: {total: 0, local: 0, num_calls: 0, max_total: 0}, tactics: []},
        ]
      });
    });

    test("ltacprof", async function () {
      const results = await parse(`<ltacprof total_time="10.1">${ltacprof_tactic('abc',0,0,0,0,[])}${ltacprof_tactic('foo',1,2,3,4,[])}</ltacprof>`);
      assert.deepStrictEqual(results,[{
        total_time: 10.1,
        tactics: [
          {name: "abc", statistics: {total: 0, local: 0, num_calls: 0, max_total: 0}, tactics: []},
          {name: "foo", statistics: {total: 1, local: 2, num_calls: 3, max_total: 4}, tactics: []},
        ]}]);
    });

    test("feedback_content - ltacprof", async function () {
      const results = await parse(`<feedback_content val="custom"><option val="none"/><string>ltacprof_results</string><ltacprof total_time="10.1">${ltacprof_tactic('abc',0,0,0,0,[])}${ltacprof_tactic('foo',1,2,3,4,[])}</ltacprof></feedback_content>`);
      assert.deepStrictEqual(results,[{
        feedbackKind: 'ltacprof',
        total_time: 10.1,
        tactics: [
          {name: "abc", statistics: {total: 0, local: 0, num_calls: 0, max_total: 0}, tactics: []},
          {name: "foo", statistics: {total: 1, local: 2, num_calls: 3, max_total: 4}, tactics: []},
        ]}]);
    });

  });

  test("feedback", async function () {
    const results = await parse([
      '<feedback object="state" route="1"><state_id val="5"/><feedback_content val="errormsg"><loc start="1" stop="3"/><string>hi</string></feedback_content></feedback>',
      '<feedback object="edit"><edit_id val="4"/><feedback_content val="errormsg"><loc start="1" stop="3"/><string>hi</string></feedback_content></feedback>',
    ]);
    assert.deepStrictEqual(results[0], {
      objectId: {objectKind: "stateid", stateId: 5},
      route: 1,
      feedbackKind: "message",
      level: proto.MessageLevel.Error,
      location: {start: 1, stop: 3}, message: "hi"
    });
    assert.deepStrictEqual(results[1], {
      objectId: {objectKind: "editid", editId: 4},
      route: 0,
      feedbackKind: "message",
      level: proto.MessageLevel.Error,
      location: {start: 1, stop: 3}, message: "hi"
    });
  });

  test("goal", async function () {
    const results = await parse([
      '<goal><int>5</int><list/><string>True</string></goal>',
      '<goal><int>5</int><list><string>hi</string></list><string>True</string></goal>',
      '<goal><int>5</int><list><string>hi</string><richpp><_><aa>t</aa>h<bb>er</bb>e</_></richpp></list><string>True</string></goal>',
      ]);
    results.forEach((g:proto.Subgoal) => {
      g.hypotheses = g.hypotheses.map((h)=>text.normalizeText(h));
      g.goal = text.normalizeText(g.goal)
    })
    assert.deepStrictEqual(results, [
      {id: 5, hypotheses: [], goal: "True"},
      {id: 5, hypotheses: ["hi"], goal: "True"},
      {id: 5, hypotheses: ["hi", {scope:"_",text:[{scope: "aa", text:"t"},"h",{scope: "bb", text:"er"},"e"]}], goal: "True"},
    ]);
  });

  test("goals", async function () {
    const results = await parse([
      '<goals><list/><list/><list/><list/></goals>',
      '<goals><list><goal><int>5</int><list/><string>True</string></goal></list><list/><list><goal><int>5</int><list/><string>True</string></goal></list><list><goal><int>5</int><list/><string>True</string></goal></list></goals>',
      '<goals><list/><list><pair><list/><list/></pair></list><list/><list/></goals>',
      '<goals><list/><list><pair><list><goal><int>1</int><list/><string>True</string></goal></list><list><goal><int>2</int><list/><string>True</string></goal></list></pair></list><list/><list/></goals>',
      '<goals><list/><list><pair><list><goal><int>1</int><list/><string>True</string></goal><goal><int>2</int><list/><string>True</string></goal></list><list><goal><int>3</int><list/><string>True</string></goal><goal><int>4</int><list/><string>True</string></goal></list></pair></list><list/><list/></goals>',
      '<goals><list/><list><pair><list><goal><int>1</int><list/><string>True</string></goal></list><list><goal><int>2</int><list/><string>True</string></goal></list></pair><pair><list><goal><int>3</int><list/><string>True</string></goal></list><list><goal><int>4</int><list/><string>True</string></goal></list></pair></list><list/><list/></goals>',
      ]);
    assert.deepStrictEqual(results[0], {goals: [], backgroundGoals: null, shelvedGoals: [], abandonedGoals: []});
    assert.deepStrictEqual(results[1], {goals: [{id: 5, hypotheses: [], goal: "True"}], backgroundGoals: null, shelvedGoals: [{id: 5, hypotheses: [], goal: "True"}], abandonedGoals: [{id: 5, hypotheses: [], goal: "True"}]});
    assert.deepStrictEqual(results[2], {
      goals: [],
      backgroundGoals: {before: [], next: null, after: []},
      shelvedGoals: [],
      abandonedGoals: []});
    assert.deepStrictEqual(results[3], {
      goals: [],
      backgroundGoals: {
        before: [{id: 1, hypotheses: [], goal: "True"}],
        next: null,
        after: [{id: 2, hypotheses: [], goal: "True"}]},
      shelvedGoals: [],
      abandonedGoals: []});
    assert.deepStrictEqual(results[4], {
      goals: [],
      backgroundGoals: {
        before: [{id: 1, hypotheses: [], goal: "True"}, {id: 2, hypotheses: [], goal: "True"}],
        next: null,
        after: [{id: 3, hypotheses: [], goal: "True"}, {id: 4, hypotheses: [], goal: "True"}]},
      shelvedGoals: [],
      abandonedGoals: []});
    assert.deepStrictEqual(results[5], {
      goals: [],
      backgroundGoals: {
        before: [{id: 3, hypotheses: [], goal: "True"}],
        next: {
          before: [{id: 1, hypotheses: [], goal: "True"}],
          next: null,
          after: [{id: 2, hypotheses: [], goal: "True"}]},
        after: [{id: 4, hypotheses: [], goal: "True"}]},
      shelvedGoals: [],
      abandonedGoals: []});
  });

});