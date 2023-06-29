import React, {FunctionComponent, KeyboardEvent, ChangeEventHandler} from 'react';
import {
    VSCodeButton, 
    VSCodePanelView, 
    VSCodePanelTab, 
    VSCodePanels
} from '@vscode/webview-ui-toolkit/react';
import {VscAdd, VscChromeClose} from 'react-icons/vsc';

import SearchField from '../molecules/SearchField';
import Dropdown from '../molecules/Dropdown';
import ResultTabs from '../organisms/ResultTabs';
import ResultSection from '../organisms/ResultSection';
import ResultPage from '../organisms/ResultPage';

import classes from './SearchPage.module.css';

import { QueryPanelState } from '../../types';

type SearchPageProps = {

    state: QueryPanelState,
    copyNameHandler: (name: string) => void,
    queryTypeSelectHandler: (e: any) => void;
    onTextInput: (e: any) => void; //FormEventHandler<HTMLInputElement>
    searchFieldKeyPressHandler: (index:number, e: KeyboardEvent<HTMLInputElement>) => void,
    addTabHandler: () => void,
    deleteTabHandler: (tabIndex: number) => void,
    changeTabHandler: (tabIndex: number) => void,
    tabInputHandler: (index: number, field: string) => (ChangeEventHandler<HTMLInputElement>)
};

const searchPage: FunctionComponent<SearchPageProps> = (props) => {
    
    const {
        state, 
        copyNameHandler, 
        onTextInput, searchFieldKeyPressHandler,
        changeTabHandler, addTabHandler, 
        deleteTabHandler,
        queryTypeSelectHandler, 
        tabInputHandler
    } = props;

    const {tabs, currentTab} = state;

    const panelViews = tabs.map((tab, index) => {
        const id = "view-" + index;
        return (
            <VSCodePanelView key={id} id={id} >
                <ResultPage 
                    tab={tab}
                    queryTypeSelectHandler={tabInputHandler(index, "type")}
                    onTextInput={tabInputHandler(index, "pattern")}
                    searchFieldKeyPressHandler={(e) => searchFieldKeyPressHandler(index, e)}
                    copyNameHandler={copyNameHandler}
                />
            </VSCodePanelView>
        );
    });

    const panelTabs = tabs.map((tab, index) => {
        const id = "tab-" + index;
        return <VSCodePanelTab 
                    id={id} 
                    key={id}
                    
                    onClick={
                        () => changeTabHandler(index)
                    }
                    aria-selected={currentTab === index}
                    className={tabs.length > 1 ? "" : classes.HiddenTab} //hide the tabs if there is only one
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
            <VSCodePanels className={classes.Panels}>
                <div className={classes.PageHeader}>
                    <VSCodeButton 
                        className={classes.Button}
                        appearance={'icon'} 
                        ariaLabel='Add Tab' 
                        onClick={() => addTabHandler()}
                    >
                        <VscAdd />
                    </VSCodeButton>
                </div>
                {panelTabs}
                {panelViews}
            </VSCodePanels>
            </div>
    );
};

export default searchPage;