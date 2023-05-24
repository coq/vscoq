import { expect } from 'expect';
import * as path from 'node:path';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as vscode from 'vscode';
// import * as myExtension from '../../extension';

async function openTextFile(file : string) : Promise<vscode.Uri> {
  const docUri = vscode.Uri.file(path.resolve(__dirname, '../../../testFixture', file));
  const doc = await vscode.workspace.openTextDocument(docUri);
  await vscode.window.showTextDocument(doc, { preview : false });
  return docUri;
}

suite('Should get diagnostics', function () {

	this.timeout(60000);

	test('Diagnoses an undefined ref error', async () => {

        const doc = await openTextFile('basic.v');

		const ext = vscode.extensions.getExtension('coq-community.vscoq')!;
		await ext.activate();
        
		await sleep(10000); // Wait for server initialization

		const diagnostics = vscode.languages.getDiagnostics(doc);
		
		expect(diagnostics.length).toBe(1);

		const diagnostic = diagnostics[0];

		expect(diagnostic.message).toMatch(/The reference zar was not found.*/);
		
		expect(diagnostic.severity).toBe(vscode.DiagnosticSeverity.Error);
	
	});


	test('Opens two files and gets feedback', async () => {

		const ext = vscode.extensions.getExtension('coq-community.vscoq')!;
		await ext.activate();

        const doc1 = await openTextFile('basic.v');

		await sleep(10000); // Wait for server initialization

		const doc2 = await openTextFile('warn.v');

		await sleep(10000); // Wait for server initialization

		const diagnostics1 = vscode.languages.getDiagnostics(doc1);
		const diagnostics2 = vscode.languages.getDiagnostics(doc2);

		expect(diagnostics1.length).toBe(1);
		expect(diagnostics2.length).toBe(1);
	
	});


	test('Opens two files and gets feedback in the appropriate tab', async () => {

		const ext = vscode.extensions.getExtension('coq-community.vscoq')!;
		await ext.activate();

        const doc1 = await openTextFile('basic.v');

		const doc2 = await openTextFile('warn.v');

		await sleep(10000); // Wait for server initialization

		const diagnostics1 = vscode.languages.getDiagnostics(doc1);
		const diagnostics2 = vscode.languages.getDiagnostics(doc2);

		expect(diagnostics1.length).toBe(1);
		expect(diagnostics1[0].message).toMatch(/The reference zar was not found.*/);
		expect(diagnostics1[0].severity).toBe(vscode.DiagnosticSeverity.Error);

		expect(diagnostics2.length).toBe(1);
		expect(diagnostics2[0].message).toMatch(/.*There is no flag or option.*/);
		expect(diagnostics2[0].severity).toBe(vscode.DiagnosticSeverity.Error); // BUG, should be warning
	
	});

	test('Opens two files and gets feedback in the appropriate tab (with proof delegation)', async () => {

		const ext = vscode.extensions.getExtension('coq-community.vscoq')!;
		await ext.activate();

		// vscode.workspace.getConfiguration().update('vscoq.proof.delegation','Skip');
		vscode.workspace.getConfiguration().update('vscoq.proof.delegation','Delegate');

		const doc1 = await openTextFile('delegate_proof.v');

		const doc2 = await openTextFile('warn.v');

		await sleep(10000); // Wait for server initialization

		const diagnostics1 = vscode.languages.getDiagnostics(doc1);
		const diagnostics2 = vscode.languages.getDiagnostics(doc2);

		expect(diagnostics1.length).toBe(2);
		expect(diagnostics1[1].message).toMatch(/.*foobar was not found.*/);
		expect(diagnostics1[1].severity).toBe(vscode.DiagnosticSeverity.Error);
		expect(diagnostics1[0].message).toMatch(/.*Attempt to save an incomplete proof.*/);
		expect(diagnostics1[0].severity).toBe(vscode.DiagnosticSeverity.Error);

		expect(diagnostics2.length).toBe(1);
		expect(diagnostics2[0].message).toMatch(/.*There is no flag or option.*/);
		expect(diagnostics2[0].severity).toBe(vscode.DiagnosticSeverity.Error); // BUG, should be warning
	
	});


});

async function sleep(ms: number) {
	return new Promise(resolve => setTimeout(resolve, ms));
}