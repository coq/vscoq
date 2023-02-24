import React, {FunctionComponent} from 'react';

import {
    VSCodeOption, 
    VSCodeDropdown,
} from '@vscode/webview-ui-toolkit/react';

type DropdownProps = {
    onChange: (e:any) => void;
    selectedValue: string; 
    options: string[];
    optionLabels?: string[];
    classes: string[];
};

const dropdown: FunctionComponent<DropdownProps> = (props) => {
    const {options, optionLabels, selectedValue, onChange, classes} = props;

    return (
        <VSCodeDropdown className={classes.join(' ')} onChange={e => onChange(e)}>
            {
                options.map((opt, index) => {
                    const label = optionLabels ? optionLabels[index] : opt;
                    return (
                        <VSCodeOption key={index} value={opt} selected={opt === selectedValue}>{label}</VSCodeOption>
                    );
                })
            }
        </VSCodeDropdown>
    );
};

export default dropdown;