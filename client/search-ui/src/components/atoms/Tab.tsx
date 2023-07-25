import React, {FunctionComponent} from 'react';

import classes from './Tab.module.css';
import { VSCodeButton } from '@vscode/webview-ui-toolkit/react';
import { VscChromeClose } from 'react-icons/vsc';

type TabProps = {
    isSelected: boolean;
    closeTabHandler: () => void;
    onClick: () => void;
};

const tab: FunctionComponent<TabProps> = (props) => {
    
    const {isSelected, onClick, closeTabHandler} = props;

    let classNames = isSelected ? [classes.Tab, classes.Active] : [classes.Tab, classes.Inactive]; 

    return (
        <div 
            className={classNames.join(' ')}
            onClick={onClick}
        >
            <div className={classes.Text}>
                {props.children}
            </div>
            
            <VSCodeButton 
                className={classes.SmallButton}
                appearance={'icon'} 
                ariaLabel='Delete' 
                onClick={(event) => {
                    event.stopPropagation();
                    closeTabHandler();
                }}
            >
                <VscChromeClose />
            </VSCodeButton>
        </div>
    );
}; 

export default tab;