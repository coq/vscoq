import React, {FunctionComponent} from 'react';

import classes from './Tab.module.css';
import { VSCodeButton } from '@vscode/webview-ui-toolkit/react';
import { VscChromeClose } from 'react-icons/vsc';

type TabProps = {
    isSelected: boolean;
    noClose?: boolean;
    closeTabHandler: () => void;
    onClick: () => void;
};

const tab: FunctionComponent<TabProps> = (props) => {
    
    const {isSelected, onClick, closeTabHandler, noClose = false} = props;

    const classNames = isSelected ? [classes.Tab, classes.Active] : [classes.Tab, classes.Inactive]; 
    const buttonClassNames = noClose ? [classes.SmallButton, classes.Hidden] : [classes.SmallButton];

    return (
        <div 
            className={classNames.join(' ')}
            onClick={onClick}
        >
            <div className={classes.Text}>
                {props.children}
            </div>
            
            <VSCodeButton 
                className={buttonClassNames.join(' ')}
                disabled={noClose}
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