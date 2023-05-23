import { expect } from 'expect';
import * as path from 'node:path';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as vscode from 'vscode';
// import * as myExtension from '../../extension';

async function openTextFile(file : string) {
  const docUri = vscode.Uri.file(path.resolve(__dirname, '../../../testFixture', file));
  const doc = await vscode.workspace.openTextDocument(docUri);
  await vscode.window.showTextDocument(doc, { preview : false });
}

suite('Should get diagnostics', function () {

	this.timeout(50000);

	test('Diagnoses an undefined ref error', async () => {

        await openTextFile('basic.v');

		const ext = vscode.extensions.getExtension('coq-community.vscoq')!;
		await ext.activate();
        
		await sleep(10000); // Wait for server initialization

		const allDiagnostics = vscode.languages.getDiagnostics();

		expect(allDiagnostics.length).toBe(1);

		const [uri, diagnostics] = allDiagnostics[0];
		
		expect(diagnostics.length).toBe(1);

		const diagnostic = diagnostics[0];

		expect(diagnostic.message).toMatch(/The reference zar was not found.*/);
		
		expect(diagnostic.severity).toBe(vscode.DiagnosticSeverity.Error);
	
	});


	test('Opens two files and gets feedback', async () => {


		const ext = vscode.extensions.getExtension('coq-community.vscoq')!;
		await ext.activate();

        await openTextFile('basic.v');

		await sleep(10000); // Wait for server initialization

		await openTextFile('warn.v');

		await sleep(10000); // Wait for server initialization

		const allDiagnostics = vscode.languages.getDiagnostics();

		expect(allDiagnostics.length).toBe(2);
	
	});


	test('Opens two files and gets feedback in the appropriate tab', async () => {


		const ext = vscode.extensions.getExtension('coq-community.vscoq')!;
		await ext.activate();

        await openTextFile('basic.v');

		await openTextFile('warn.v');

		await sleep(10000); // Wait for server initialization

		const allDiagnostics = vscode.languages.getDiagnostics();

		expect(allDiagnostics.length).toBe(2);

		const [uri1, diagnostics1] = allDiagnostics[0];
		const [uri2, diagnostics2] = allDiagnostics[1];

		expect(uri1.toString()).toMatch(/.*basic.v/);
		expect(diagnostics1.length).toBe(1);
		expect(diagnostics1[0].message).toMatch(/The reference zar was not found.*/);
		expect(diagnostics1[0].severity).toBe(vscode.DiagnosticSeverity.Error);

		expect(uri2.toString()).toMatch(/.*warn.v/);
		expect(diagnostics2.length).toBe(1);
		expect(diagnostics2[0].message).toMatch(/.*There is no flag or option.*/);
		expect(diagnostics2[0].severity).toBe(vscode.DiagnosticSeverity.Error); // BUG, should be warning
	
	});


});

async function sleep(ms: number) {
	return new Promise(resolve => setTimeout(resolve, ms));
}