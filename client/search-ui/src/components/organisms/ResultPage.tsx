import React, {FunctionComponent, KeyboardEventHandler} from 'react';

import { QueryTab } from '../../types';

import QueryBar from '../molecules/QueryBar';
import ResultSection from './ResultSection';
import Error from '../atoms/Error';

type ResultPageProps = {
    tab: QueryTab;
    queryTypeSelectHandler: (e: any) => void;
    onTextInput: (e: any) => void; //FormEventHandler<HTMLInputElement>
    searchFieldKeyPressHandler: KeyboardEventHandler<HTMLInputElement>,
    toggleCollapsedHandler: (index: number) => void;
    deleteSearchResultHandler: (index: number) => void;
    copyNameHandler: (name: string) => void;
};

const page: FunctionComponent<ResultPageProps> = (props) => {

    const {
        tab,
        queryTypeSelectHandler, 
        onTextInput, 
        searchFieldKeyPressHandler,
        toggleCollapsedHandler,
        deleteSearchResultHandler,
        copyNameHandler
    } = props;

    const {pattern, error, result, type} = tab;

    const errorSection = error ? <Error error={error} /> : null;

    return (
        <div>
            <QueryBar 
                tabInput={{
                    pattern,
                    type,
                }}
                queryTypeSelectHandler={queryTypeSelectHandler}
                onTextInput={onTextInput}
                searchFieldKeyPressHandler={searchFieldKeyPressHandler}
            />
            {errorSection}
            <ResultSection 
                result={result}
                toggleCollapsedHandler={toggleCollapsedHandler}
                deleteSearchResultHandler={deleteSearchResultHandler}
                copyNameHandler={copyNameHandler}
            />
        </div>
    );
};

export default page;