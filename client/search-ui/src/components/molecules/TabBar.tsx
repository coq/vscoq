import React, {FunctionComponent} from 'react';

import Tab from '../atoms/Tab';

import classes from './TabBar.module.css';

type TabBarProps = {
    selected: number; 
    tabNames: string[];
    tabClickHandler: (i: number) => void;
    closeTabHandler: (i: number) => void;
};

const tabBar: FunctionComponent<TabBarProps> = (props) => {
    
    const {selected, tabNames, tabClickHandler, closeTabHandler} = props;

    const tabs = tabNames.map((name, index) => {
        return (
            <Tab 
                key={index}
                isSelected={index === selected}
                closeTabHandler={() => closeTabHandler(index)}
                onClick={() => tabClickHandler(index)}
                noClose={tabNames.length === 1}
            >
                {name}
            </Tab>
        );
    });

    return (
        <div className={classes.Bar}>
            {tabs}
        </div>
    );
};

export default tabBar;