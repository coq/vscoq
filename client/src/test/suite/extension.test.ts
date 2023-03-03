import { expect } from 'expect';
import * as path from 'node:path';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as vscode from 'vscode';
// import * as myExtension from '../../extension';

async function openTextFile(file : string) {
  const docUri = vscode.Uri.file(path.resolve(__dirname, '../../../testFixture', file));
  const doc = await vscode.workspace.openTextDocument(docUri);
  await vscode.window.showTextDocument(doc);
}

suite('Should get diagnostics', function () {

	this.timeout(30000);

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

});

async function sleep(ms: number) {
	return new Promise(resolve => setTimeout(resolve, ms));
}