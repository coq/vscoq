import React, {FunctionComponent, KeyboardEvent, ChangeEventHandler, useMemo} from 'react';

import ResultPage from '../organisms/ResultPage';
import TabBar from '../molecules/TabBar';

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

    const panels = useMemo(() => {
        return tabs.map((tab, index) => {
            return (
                <ResultPage
                    tab={tab}
                    queryTypeSelectHandler={tabInputHandler(index, "type")}
                    onTextInput={tabInputHandler(index, "pattern")}
                    searchFieldKeyPressHandler={(e) => searchFieldKeyPressHandler(index, e)}
                    copyNameHandler={copyNameHandler}
                /> 
            );
        });
    }, tabs);

    const tabNames = tabs.map(tab => tab.pattern === "" ? 'New Query' : tab.type + ': ' + tab.pattern);

    return (
            <div className={classes.Page}>
                <TabBar 
                    selected={currentTab} 
                    tabNames={tabNames} 
                    tabClickHandler={changeTabHandler} 
                    closeTabHandler={deleteTabHandler}
                />
                <div className={classes.Panel}>
                    {panels ? panels[currentTab] : null}
                </div>
            </div>
    );
};

export default searchPage;