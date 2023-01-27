import React, {FunctionComponent, KeyboardEventHandler} from 'react';

import SearchResultSection from '../organisms/SearchResultSection';
import SearchField from '../molecules/SearchField';

type SearchPageProps = {
    results: {
        id: string;
        name: string; 
        statement: string;
    }[],
    copyNameHandler: (name: string) => void,
    value: string, 
    onTextInput: (e: any) => void; //FormEventHandler<HTMLInputElement>
    handleSearch: KeyboardEventHandler<HTMLInputElement>;
};

const searchPage: FunctionComponent<SearchPageProps> = (props) => {
    
    const {results, copyNameHandler, value, onTextInput, handleSearch} = props;
    
    const uniqueIds = results.map(result => result.id).filter((value, index, self) => {
        return self.indexOf(value) === index;
    });

    const goalSections = uniqueIds.map(id => {
        return <SearchResultSection 
                    results={results.filter(result => result.id === id)} 
                    copyNameHandler={copyNameHandler}
                />;
    });

    return (
        <>
            <SearchField 
                value={value} 
                onTextInput={onTextInput} 
                handleSearch={handleSearch} 
            />
            {goalSections}
        </>
    );
};

export default searchPage;