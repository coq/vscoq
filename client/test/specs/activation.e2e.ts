import * as path from "path";
import { mkdirp } from 'fs-extra';

before('should load extension and open problems view', async function () {
    this.timeout(180000);
    const workbench = await browser.getWorkbench();
    const bottomBar = await workbench.getBottomBar();
    const problemsView = await bottomBar.openProblemsView();
    return await browser.waitUntil(async () => {
        const workbench = await browser.getWorkbench();
        const notifications = await workbench.getNotifications();
        for (const n of notifications) {
          await n.dismiss();
        }
        const openNotifications = await workbench.getNotifications();
        return openNotifications.length === 0;
      });
  });

describe('VsCoq 2', () => {
    it('should be able to load VS Code', async () => {
        const workbench = await browser.getWorkbench();
        expect(await workbench.getTitleBar().getTitle())
            .toBe('[Extension Development Host] basic.v - Visual Studio Code');
    });

    it('should get error feedback from language server', async () => {
        const workbench = await browser.getWorkbench();
        const bottomBar = workbench.getBottomBar();
        const problemsView = await bottomBar.openProblemsView();
        mkdirp(path.join(__dirname, "screenshots"));
        await browser.saveScreenshot(
            path.join(__dirname, "../../screenshots", "before-wait.png")
        );
        await browser.waitUntil(async () => {
            const countBadge = await problemsView.getCountBadge();
            return (await countBadge.isExisting());
        }, { timeout: 30000 });
        expect(await (await problemsView.getCountBadge()).getText()).toBe('1');
    });
});