import React, {FunctionComponent} from 'react';

import SearchResult from '../molecules/SearchResult';

import classes from './SearchResultSection.module.css';

type SearchResultSectionProps = {
    results: {
        id: string, 
        name: string, 
        statement: string,
    }[],
    copyNameHandler: (name: string) => void;
};

const searchResultSection: FunctionComponent<SearchResultSectionProps> = (props) => {

    const {results, copyNameHandler} = props;

    const resultComponents = results.map(result => {
        return <SearchResult 
                    name={result.name} 
                    statement={result.statement} 
                    copyNameHandler={copyNameHandler}
                />;
    });

    return (
        <div className={classes.ResultSection}>
            {resultComponents}
        </div>
    );
};

export default searchResultSection;