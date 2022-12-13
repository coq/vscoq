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

import ResultSection from '../organisms/ResultSection';
import SearchField from '../molecules/SearchField';
import Dropdown from '../molecules/Dropdown';

import classes from './SearchPage.module.css';


type SearchPageProps = {
    tabs: {
        searchId: string,
        searchString: string, 
        results: {
            id: string, 
            name: string, 
            statement: string,
            type: string,
        }[]
    }[],
    copyNameHandler: (name: string) => void,
    value: string, 
    queryTypeSelectHandler: (e: any) => void;
    onTextInput: (e: any) => void; //FormEventHandler<HTMLInputElement>
    searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement>,
    addTabHandler: () => void,
    deleteTabHandler: (tabIndex: number) => void,
    changeTabHandler: (tabIndex: number) => void,
    currentTab: number;
    selectedType: string;
};

const searchPage: FunctionComponent<SearchPageProps> = (props) => {
    
    const {tabs, copyNameHandler, value, 
            onTextInput, searchFieldKeyPressHandler,
            changeTabHandler, addTabHandler, 
            deleteTabHandler, currentTab,
            queryTypeSelectHandler, selectedType
        } = props;

    const panelViews = tabs.map((tab, index) => {
        return <VSCodePanelView id={"view-"+index} >
                    <ResultSection 
                        results={tab.results} 
                        copyNameHandler={copyNameHandler}
                    />
                </VSCodePanelView>;
    });

    const panelTabs = tabs.map((tab, index) => {
        return <VSCodePanelTab 
                    id={"tab-" + index} 
                    onClick={
                        () => changeTabHandler(index)
                    }
                    className={tabs.length > 1 ? "" : classes.HiddenTab} //hide the tabs if there is only one
                    aria-selected={index === currentTab}
                >
                    {"Query " + (tabs.length - index)}
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
                    
                    <Dropdown 
                        classes={[classes.Dropdown]} 
                        selectedValue={selectedType} 
                        options={['Search', 'Check', 'About']} 
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
                <VSCodePanels className={classes.Panels} activeid={'tab-'+currentTab}>
                    {panelTabs}
                    {panelViews}
                </VSCodePanels>
            </div>
    );
};

export default searchPage;