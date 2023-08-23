import React, {FunctionComponent, useMemo} from 'react';

import { QueryResult, QueryType, SearchResultType  } from '../../types';

import SearchResult from '../molecules/SearchResult';
import AboutResult from '../molecules/AboutResult';
import CheckResult from '../molecules/CheckResult';
import LocateResult from '../molecules/LocateResult';
import PrintResult from '../molecules/PrintResult';

import classes from './ResultSection.module.css';

type SearchResultSectionProps = {
    result: QueryResult,
    toggleCollapsedHandler: (index: number) => void;
    deleteSearchResultHandler: (index: number) => void;
    copyNameHandler: (name: string) => void;
};

const searchResultSection: FunctionComponent<SearchResultSectionProps> = (props) => {

    const {result, toggleCollapsedHandler, deleteSearchResultHandler, copyNameHandler} = props;

    const renderResult = () => {
        switch(result.type) {
            case QueryType.search: 
                return (result as SearchResultType).data.map((res, index) => {
                        return <SearchResult
                            key={index}
                            name={res.name} 
                            statement={res.statement} 
                            collapsed={res.collapsed}
                            copyNameHandler={copyNameHandler}
                            toggleCollapsedHandler={() => toggleCollapsedHandler(index)}
                            deleteResultHandler={() => deleteSearchResultHandler(index)}
                        />;
                    });

            case QueryType.check:
                return <CheckResult  statement={result.statement} />;

            case QueryType.about:
                return <AboutResult  statement={result.statement} />;

            case QueryType.locate: 
                return <LocateResult statement={result.statement} />;

            case QueryType.print: 
                return <PrintResult statement={result.statement} />;

        }
    };

    const resultComponent = useMemo(renderResult, [result]);

    return (
        <div className={classes.ResultSection}>
            {resultComponent}
        </div>
    );
};

export default searchResultSection;