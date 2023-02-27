import React, {FunctionComponent, KeyboardEventHandler} from 'react';
import {
    VSCodeButton
} from '@vscode/webview-ui-toolkit/react';
import {VscAdd, VscChromeClose} from 'react-icons/vsc';

import SearchField from '../molecules/SearchField';
import Dropdown from '../molecules/Dropdown';
import ResultTabs from '../organisms/ResultTabs';

import classes from './SearchPage.module.css';

import { QueryPanelState } from '../../types';

type SearchPageProps = {

    state: QueryPanelState,
    copyNameHandler: (name: string) => void,
    queryTypeSelectHandler: (e: any) => void;
    onTextInput: (e: any) => void; //FormEventHandler<HTMLInputElement>
    searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement>,
    addTabHandler: () => void,
    deleteTabHandler: (tabIndex: number) => void,
    changeTabHandler: (tabIndex: number) => void,
};

const searchPage: FunctionComponent<SearchPageProps> = (props) => {
    
    const {
        state, 
        copyNameHandler, 
        onTextInput, searchFieldKeyPressHandler,
        changeTabHandler, addTabHandler, 
        deleteTabHandler,
        queryTypeSelectHandler
    } = props;

    const {tabs, currentTab} = state;
    const {pattern, type} = tabs[currentTab];

    return (
            <div className={classes.Page}>
                <div className={classes.PageHeader}>
                    <SearchField 
                        value={pattern} 
                        onTextInput={onTextInput} 
                        onKeyDown={searchFieldKeyPressHandler} 
                    />
                    
                    <Dropdown 
                        classes={[classes.Dropdown]} 
                        selectedValue={type} 
                        options={['search', 'check', 'about']} 
                        optionLabels={['Search', 'Check', 'About']} 
                        onChange={queryTypeSelectHandler}
                    />

                    <VSCodeButton 
                        className={classes.Button}
                        appearance={'icon'} 
                        ariaLabel='Add Tab' 
                        onClick={() => addTabHandler()}
                    >
                        <VscAdd />
                    </VSCodeButton>
                </div>
                <ResultTabs 
                    tabs={tabs}
                    currentTab={currentTab}
                    copyNameHandler={copyNameHandler}
                    changeTabHandler={changeTabHandler}
                    deleteTabHandler={deleteTabHandler}
                    searchFieldKeyPressHandler={searchFieldKeyPressHandler}
                />
            </div>
    );
};

export default searchPage;