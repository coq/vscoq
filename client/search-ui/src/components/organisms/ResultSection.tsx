import React, {FunctionComponent} from 'react';

import { QueryResult  } from '../../types';

import SearchResult from '../molecules/SearchResult';
import AboutResult from '../molecules/AboutResult';
import CheckResult from '../molecules/CheckResult';
import LocateResult from '../molecules/LocateResult';
import PrintResult from '../molecules/PrintResult';

import classes from './ResultSection.module.css';

type SearchResultSectionProps = {
    result: QueryResult,
    toggleCollapsedHandler: (index: number) => void;
    copyNameHandler: (name: string) => void;
};

const searchResultSection: FunctionComponent<SearchResultSectionProps> = (props) => {

    const {result, toggleCollapsedHandler, copyNameHandler} = props;

    let resultComponent = null; 

    if(result.type === "search") {

        resultComponent = result.data.map((res, index) => {

            return <SearchResult
                key={index}
                name={res.name} 
                statement={res.statement} 
                collapsed={res.collapsed}
                copyNameHandler={copyNameHandler}
                toggleCollapsedHandler={() => toggleCollapsedHandler(index)}
            />;
    
        });
    
    }

    if(result.type === "check") {
        
        resultComponent = <CheckResult  statement={result.statement} />;

    };

    if(result.type === "about") {
            
        resultComponent = <AboutResult  statement={result.statement} />;
        
    };

    if(result.type === "locate") {
        resultComponent = <LocateResult statement={result.statement} />;
    }

    if(result.type === "print") {
        resultComponent = <PrintResult statement={result.statement} />;
    }

    return (
        <div className={classes.ResultSection}>
            {resultComponent}
        </div>
    );
};

export default searchResultSection;