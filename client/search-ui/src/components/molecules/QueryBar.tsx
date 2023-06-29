import React, {FunctionComponent, KeyboardEventHandler} from 'react';
import {
    VSCodeButton
} from'@vscode/webview-ui-toolkit/react';

import Dropdown from './Dropdown';
import SearchField from './SearchField';

import classes from './QueryBar.module.css';

type QueryBarProps = {
    tabInput: {
        pattern: string, 
        type: string, 
    }
    queryTypeSelectHandler: (e: any) => void;
    onTextInput: (e: any) => void; //FormEventHandler<HTMLInputElement>
    searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement>,
};

const queryBar: FunctionComponent<QueryBarProps> = (props) => {
    
    const {
        tabInput, 
        queryTypeSelectHandler, 
        onTextInput, 
        searchFieldKeyPressHandler, 
    } = props; 

    const {pattern, type} = tabInput;

    return (
        <div className={classes.QueryBar}>

            <SearchField 
                value={pattern} 
                onTextInput={onTextInput} 
                onKeyDown={searchFieldKeyPressHandler} 
            />
                    
            <Dropdown 
                classes={[classes.Dropdown]} 
                selectedValue={type} 
                options={['search', 'check', 'about', 'locate', 'print']} 
                optionLabels={['Search', 'Check', 'About', 'Locate', 'Print']} 
                onChange={queryTypeSelectHandler}
            />

        </div>
    );
};

export default queryBar;