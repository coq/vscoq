import React, {FunctionComponent} from 'react';

import { QueryResult, SearchResultType, CheckResultType, AboutResultType  } from '../../types';

import SearchResult from '../molecules/SearchResult';
import AboutResult from '../molecules/AboutResult';
import CheckResult from '../molecules/CheckResult';

import classes from './ResultSection.module.css';

type SearchResultSectionProps = {
    result: QueryResult,
    copyNameHandler: (name: string) => void;
};

type SearchResults = SearchResultType[];

const searchResultSection: FunctionComponent<SearchResultSectionProps> = (props) => {

    const {result, copyNameHandler} = props;

    let resultComponent = null; 

    if(result.type === "search") {

        resultComponent = result.data.map((res, index) => {

            return <SearchResult
                key={index}
                name={res.name} 
                statement={res.statement} 
                copyNameHandler={copyNameHandler}
            />;
    
        });
    
    }

    if(result.type === "check") {
        
        resultComponent = <CheckResult  statement={result.statement} />;

    };

    if(result.type === "about") {
            
        resultComponent = <AboutResult  statement={result.statement} />;
        
    };

    return (
        <div className={classes.ResultSection}>
            {resultComponent}
        </div>
    );
};

export default searchResultSection;