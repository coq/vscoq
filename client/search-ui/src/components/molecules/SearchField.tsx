import React, {FunctionComponent} from 'react'; 
import { VSCodeTextField } from '@vscode/webview-ui-toolkit/react';
import {VscSearch} from 'react-icons/vsc';


const searchField: FunctionComponent = () => {

    return (
            <VSCodeTextField>
                Search
                <span slot="start">
                    <VscSearch />
                </span>
            </VSCodeTextField>
    );
};

export default searchField;