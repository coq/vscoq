import React, {FunctionComponent} from 'react';

import {
    VSCodeOption, 
    VSCodeDropdown,
} from '@vscode/webview-ui-toolkit/react';

type DropdownProps = {
    onChange: (e:any) => void;
    selectedValue: string; 
    options: string[];
    classes: string[];
};

const dropdown: FunctionComponent<DropdownProps> = (props) => {
    const {options, selectedValue, onChange, classes} = props;

    return (
        <VSCodeDropdown className={classes.join(' ')} onChange={e => onChange(e)}>
            {
                options.map(opt => {
                    return (
                        <VSCodeOption selected={opt === selectedValue}>{opt}</VSCodeOption>
                    );
                })
            }
        </VSCodeDropdown>
    );
};

export default dropdown;