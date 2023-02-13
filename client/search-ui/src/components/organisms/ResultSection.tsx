import React, {FunctionComponent} from 'react';

import SearchResult from '../molecules/SearchResult';
import AboutResult from '../molecules/AboutResult';

import classes from './ResultSection.module.css';

type SearchResultSectionProps = {
    results: {
        id: string, 
        name: string, 
        statement: string,
        type: string,
    }[],
    copyNameHandler: (name: string) => void;
};

const searchResultSection: FunctionComponent<SearchResultSectionProps> = (props) => {

    const {results, copyNameHandler} = props;

    const resultComponents = results.map(result => {

        if(result.type === "Search") {

            return <SearchResult 
                        name={result.name} 
                        statement={result.statement} 
                        copyNameHandler={copyNameHandler}
                    />;

        }

        if(result.type === "About") {

            return <AboutResult  statement={result.statement} />;

        }

        return; 
    });

    return (
        <div className={classes.ResultSection}>
            {resultComponents}
        </div>
    );
};

export default searchResultSection;