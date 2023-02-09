import React, {FunctionComponent, KeyboardEventHandler} from 'react';
import {
    VSCodePanels,
    VSCodePanelTab,
    VSCodePanelView,
    VSCodeButton,
    VSCodeDropdown,
    VSCodeOption
} from '@vscode/webview-ui-toolkit/react';
import {VscAdd, VscChromeClose} from 'react-icons/vsc';

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
    deleteTabHandler: (tabIndex: number) => void,
    changeTabHandler: (tabIndex: number) => void,
    currentTab: number;
};

const searchPage: FunctionComponent<SearchPageProps> = (props) => {
    
    const {tabs, copyNameHandler, value, 
            onTextInput, searchFieldKeyPressHandler,
            changeTabHandler, addTabHandler, deleteTabHandler, currentTab} = props;

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
                    aria-selected={index === currentTab}
                >
                    {"Search " + index}
                    <VSCodeButton 
                        className={classes.SmallButton}
                        appearance={'icon'} 
                        ariaLabel='Add Tab' 
                        onClick={() => deleteTabHandler(index)}
                    >
                        <VscChromeClose />
                    </VSCodeButton>
                </VSCodePanelTab>;
    });

    return (
            <div className={classes.Page}>
                <div className={classes.PageHeader}>
                    <SearchField 
                        value={value} 
                        onTextInput={onTextInput} 
                        onKeyDown={searchFieldKeyPressHandler} 
                    />

                    <VSCodeDropdown className={classes.Dropdown} onChange={(event) => {console.log(event); }}>
                        <VSCodeOption>Search</VSCodeOption>
                        <VSCodeOption>Check</VSCodeOption>
                        <VSCodeOption>About</VSCodeOption>
                    </VSCodeDropdown>

                    <VSCodeButton 
                        className={classes.Button}
                        appearance={'icon'} 
                        ariaLabel='Add Tab' 
                        onClick={() => addTabHandler()}
                    >
                        <VscAdd />
                    </VSCodeButton>
                </div>
                <VSCodePanels className={classes.Panels}>
                    {panelTabs}
                    {panelViews}
                </VSCodePanels>
            </div>
    );
};

export default searchPage;