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

const searchResultSection: FunctionComponent<SearchResultSectionProps> = (props) => {

    const {result, copyNameHandler} = props;

    let resultComponent = null; 

    if(result as SearchResultType[]) {

        resultComponent = (result as SearchResultType[]).map((res) => {

            return <SearchResult 
                name={res.name} 
                statement={res.statement} 
                copyNameHandler={copyNameHandler}
            />;
    
        });
    
    }

    if(result as CheckResultType) {
        
        resultComponent = <CheckResult  statement={result as CheckResultType} />;

    };

    if(result as AboutResultType) {
            
        resultComponent = <AboutResult  statement={result as AboutResultType} />;
        
    };

    return (
        <div className={classes.ResultSection}>
            {resultComponent}
        </div>
    );
};

export default searchResultSection;