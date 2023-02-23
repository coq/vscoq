import React, {FunctionComponent, KeyboardEventHandler} from 'react';
import {
    VSCodePanels,
    VSCodePanelTab,
    VSCodePanelView,
    VSCodeButton
} from '@vscode/webview-ui-toolkit/react';
import {VscAdd, VscChromeClose} from 'react-icons/vsc';

import ResultSection from '../organisms/ResultSection';

import { QueryTab } from '../../types';

import classes from './ResultTabs.module.css';

type ResultTabProps = {
    tabs: QueryTab[],
    currentTab: number,
    copyNameHandler: (name: string) => void,
    changeTabHandler: (tabIndex: number) => void,
    deleteTabHandler: (tabIndex: number) => void,
    searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement>,
};

const resultTabs: FunctionComponent<ResultTabProps> = (props) => {
    
    const {
        tabs, currentTab, 
        copyNameHandler, changeTabHandler, deleteTabHandler, 
        searchFieldKeyPressHandler
    } = props;

    const panelViews = tabs.map((tab, index) => {
        return <VSCodePanelView id={"view-"+index} >
                    <ResultSection 
                        result={tab.results} 
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
        <VSCodePanels className={classes.Panels} activeid={'tab-'+currentTab}>
            {panelTabs}
            {panelViews}
        </VSCodePanels>
    );
};

export default resultTabs;