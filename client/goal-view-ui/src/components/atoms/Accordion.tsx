import React, {FunctionComponent, useEffect, useState} from 'react';
import {VSCodeButton} from '@vscode/webview-ui-toolkit/react';
import {VscChevronDown} from 'react-icons/vsc';

import classes from './Accordion.module.css';

type AccordionProps = {
    collapsed: boolean;
    title: string;
    collapseHandler?: (params: any) => void;
};

const accordion: FunctionComponent<AccordionProps> = (props) => {
    
    const {title, collapseHandler} = props;
    const [collapsed, setCollapsed] = useState(props.collapsed);
    useEffect(() => {
        setCollapsed(props.collapsed);
    }, [props.collapsed]);

    const panelClasses = [classes.Panel]; 
    if(collapsed) {
        panelClasses.push(classes.Closed);
    }

    const toggleCollapse = collapseHandler ? collapseHandler : () => setCollapsed(!collapsed);

    return (
        <div className={classes.Block}>

            {/* The header with title and button */}
            <div className={classes.Header}>
                <span className={!collapsed ? classes.Demphasize : ''}>{title}</span>
                <VSCodeButton appearance={'icon'} ariaLabel='Collapse' onClick={toggleCollapse}>
                    <VscChevronDown className={!collapsed ? [classes.Rotated, classes.Demphasize].join(' ') : ''} />
                </VSCodeButton>
            </div>

            {/* The panel that collapses */}
            <div className={panelClasses.join(' ')}>
                {props.children}
            </div>
                

        </div>
    );

};

export default accordion;