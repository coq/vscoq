import * as React from 'react';
import { vscode } from "./utilities/vscode";
import { VSCodeButton } from "@vscode/webview-ui-toolkit/react";
import "./App.css";
import { DidChangeWorkspaceFoldersNotification } from 'vscode-languageclient';
import { PropertyStyleSheetBehavior } from '@microsoft/fast-foundation';

interface Props {

}

interface State {
  goals: String
}

class App extends React.Component<Props,State> {
  constructor(props: any) {
    super(props);
    this.state = { goals: "" };
    window.addEventListener("message", this.handleMessage.bind(this));
  }

  private handleHowdyClick() {
    vscode.postMessage({
      command: "hello",
      text: "Hey there partner! 🤠",
    });
  }

  private handleMessage(msg: any) {
    switch (msg.data.command) {
      case 'renderProofView':
        this.setState(() => ({goals: msg.data.text.goals[0].goal}));
      break;
    }
  }

  render() {
    return (
    <main>
      <h1>{this.state.goals}</h1>
      <VSCodeButton onClick={this.handleHowdyClick}>Howdy!</VSCodeButton>
    </main>
  );
    }
}

export default App;
