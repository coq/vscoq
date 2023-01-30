import React, {FunctionComponent, KeyboardEventHandler, FormEventHandler, FormEvent, useState} from 'react'; 
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
    onKeyDown: KeyboardEventHandler<HTMLInputElement>
};

const searchField: FunctionComponent<SearchFieldProps> = (props) => {

    const {value, onTextInput, onKeyDown} = props;

    const [placeholder, setPlaceholder] = useState("Search");

    return (
        <VSCodeTextField 
            className={classes.SearchField} 
            placeholder={placeholder} 
            value={value} 
            onInput={onTextInput}
            onKeyDown={onKeyDown}
            onFocus={() => setPlaceholder("Search (↑↓ for history)")}
            onBlur={() => setPlaceholder("Search")}
        >
            <span slot="start">
                <VscSearch />
            </span>
        </VSCodeTextField>
    );
};

export default searchField;