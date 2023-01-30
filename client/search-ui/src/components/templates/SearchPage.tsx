import React, {FunctionComponent, KeyboardEventHandler, useState} from 'react';
import {
    VSCodePanels,
    VSCodePanelTab,
    VSCodePanelView,
    VSCodeButton
} from '@vscode/webview-ui-toolkit/react';
import {VscAdd} from 'react-icons/vsc';

import SearchResultSection from '../organisms/SearchResultSection';
import SearchField from '../molecules/SearchField';

import classes from './SearchPage.module.css';


type SearchPageProps = {
    tabs: {
        searchId: string,
        searchString: string, 
        results: {
            id: string, 
            name: string, 
            statement: string
        }[]
    }[],
    copyNameHandler: (name: string) => void,
    value: string, 
    onTextInput: (e: any) => void; //FormEventHandler<HTMLInputElement>
    searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement>,
    addTabHandler: () => void,
    changeTabHandler: (tabIndex: number) => void,
    currentTab: number;
};

const searchPage: FunctionComponent<SearchPageProps> = (props) => {
    
    const {tabs, copyNameHandler, value, 
            onTextInput, searchFieldKeyPressHandler,
            changeTabHandler, addTabHandler, currentTab} = props;

    const panelViews = tabs.map((tab, index) => {
        return <VSCodePanelView id={"tab-"+index} >
                    <SearchResultSection 
                        results={tab.results} 
                        copyNameHandler={copyNameHandler}
                    />
                </VSCodePanelView>;
    });

    const panelTabs = tabs.length === 1 ? null : tabs.map((tab, index) => {
        return <VSCodePanelTab 
                    id={"tab-" + index} 
                    onClick={
                        () => changeTabHandler(index)
                    }
                >
                    {"Search " + index}
                </VSCodePanelTab>;
    });

    return (
            <>
                <div className={classes.Header}>
                    <SearchField 
                        value={value} 
                        onTextInput={onTextInput} 
                        onKeyDown={searchFieldKeyPressHandler} 
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
                <VSCodePanels activeid={'tab-'+currentTab} className={classes.Panels}>
                    {panelTabs}
                    {panelViews}
                </VSCodePanels>
        </>
    );
};

export default searchPage;