import React, {FunctionComponent, useMemo} from 'react';

import { QueryResultType, QueryType, SearchResultType  } from '../../types';

import SearchResult from '../molecules/SearchResult';
import QueryResult from '../molecules/QueryResult';

import classes from './ResultSection.module.css';

type SearchResultSectionProps = {
    result: QueryResultType,
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
                            result={res}
                            copyNameHandler={copyNameHandler}
                            toggleCollapsedHandler={() => toggleCollapsedHandler(index)}
                            deleteResultHandler={() => deleteSearchResultHandler(index)}
                        />;
                    });
            case QueryType.check:
                return <QueryResult result={result} />;

            case QueryType.about:
                return <QueryResult result={result} />;

            case QueryType.locate: 
                return <QueryResult result={result} />;

            case QueryType.print: 
                return <QueryResult result={result} />;
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