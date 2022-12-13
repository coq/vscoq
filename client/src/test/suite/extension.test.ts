import { expect } from 'expect';

// You can import and use all API from the 'vscode' module
// as well as import your extension to test it
import * as vscode from 'vscode';
// import * as myExtension from '../../extension';

suite('Should get diagnostics', function () {

	this.timeout(30000);

	test('Diagnoses an undefined ref error', async () => {

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

});

async function sleep(ms: number) {
	return new Promise(resolve => setTimeout(resolve, ms));
}