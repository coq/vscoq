import React, {FunctionComponent} from 'react';

import { VSCodeButton } from '@vscode/webview-ui-toolkit/react';
import {VscCopy} from 'react-icons/vsc';

import ResultName from '../atoms/ResultName';
import ResultStatement from '../atoms/ResultStatement';

import classes from './SearchResult.module.css';

type SearchResultProps = {
    name: string;
    statement: string; 
    copyNameHandler: (name: string) => void;
};

const searchResult: FunctionComponent<SearchResultProps> = (props) => {
    
    const {name, statement, copyNameHandler} = props;

    
    return (
        <div className={classes.ResultBlock}>
            
            <div className={classes.ResultHeader}>
                <ResultName name={name} />
                <VSCodeButton appearance={'icon'} ariaLabel='Copy' onClick={() => copyNameHandler(name)}>
                    <VscCopy />
                </VSCodeButton>
            </div>
            
            <ResultStatement statement={statement}/>

        </div>
    );
};

export default searchResult;