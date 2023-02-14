import * as path from "path";
import { mkdirp } from 'fs-extra';
import { MarkerType } from "wdio-vscode-service";

describe('VsCoq 2', () => {
    it('should be able to load VS Code', async () => {
        const workbench = await browser.getWorkbench();
        expect(await workbench.getTitleBar().getTitle())
            .toBe('[Extension Development Host] basic.v - Visual Studio Code');
    });

    it('should get error feedback from language server', async () => {
        const workbench = await browser.getWorkbench();
        const bottomBar = workbench.getBottomBar();

        await browser.waitUntil(async () => {
            const problemsView = await bottomBar.openProblemsView();
            if (!problemsView) { return false }
            const markers = await problemsView.getAllVisibleMarkers(MarkerType.Any);
            return markers && markers.length === 1
          })
    });
});