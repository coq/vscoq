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
    toggleCollapsedHandler: (index: number) => void,
    changeTabHandler: (tabIndex: number) => void,
    deleteTabHandler: (tabIndex: number) => void,
    searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement>,
};

const resultTabs: FunctionComponent<ResultTabProps> = (props) => {
    
    const {
        tabs, currentTab, 
        copyNameHandler, changeTabHandler, deleteTabHandler, 
        toggleCollapsedHandler,
        searchFieldKeyPressHandler
    } = props;

    const panelViews = tabs.map((tab, index) => {
        const id = "view-" + index;
        return <VSCodePanelView key={id} id={id} >
                    <ResultSection 
                        result={tab.result} 
                        copyNameHandler={copyNameHandler}
                    />
                </VSCodePanelView>;
    });

    useEffect(() => {
        setActiveId('tab-'+currentTab);
    }, [tabs.length]);

    const view = useMemo(
        () => {

            const panelViews = tabs.map((tab, index) => {
                const id = "view-" + index;
                return (
                    <VSCodePanelView key={id} id={id} >
                        <ResultSection 
                            result={tab.result} 
                            toggleCollapsedHandler={toggleCollapsedHandler}
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
                <VSCodePanels activeid={activeId} className={classes.Panels}>
                    {panelTabs}
                    {panelViews}
                </VSCodePanels>
            );
        }, 
        [tabs]
    );

    return (
        <VSCodePanels className={classes.Panels} activeid={'tab-'+currentTab}>
            {panelTabs}
            {panelViews}
        </VSCodePanels>
    );
};

export default resultTabs;