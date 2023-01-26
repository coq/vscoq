import React, {FunctionComponent, KeyboardEventHandler, FormEventHandler, FormEvent} from 'react'; 
import { VSCodeTextField } from '@vscode/webview-ui-toolkit/react';
import {VscSearch} from 'react-icons/vsc';

import classes from './SearchField.module.css';

// Raise issue with microsoft team ?
// There seems to be an issue with the way the onInput handler is 
// defined in VSCodeTextField... 
// It is of type ((e: Event) => unkown) & FormEventHandler<HTMLInputElement>
// This does not let me type my handler function ChangeEventHandler<HTMLInputElement>
type SearchFieldProps = {
    value: string, 
    onTextInput: (e: any) => void; //FormEventHandler<HTMLInputElement>
    handleSearch: KeyboardEventHandler<HTMLInputElement>
};

const searchField: FunctionComponent<SearchFieldProps> = (props) => {

    const {value, onTextInput, handleSearch} = props;

    return (
        <VSCodeTextField 
            className={classes.SearchField} 
            placeholder="Search" 
            value={value} 
            //handleTextInput={onTextInput}
            onInput={onTextInput}
            onKeyDown={handleSearch}
        >
            <span slot="start">
                <VscSearch />
            </span>
        </VSCodeTextField>
    );
};

export default searchField;