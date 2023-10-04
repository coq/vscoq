import React, {FunctionComponent} from 'react';

import classes from './EmptyState.module.css';

type EmptyStateProps = {
    message: string, 
    icon?: JSX.Element,
};

const emptyState : FunctionComponent<EmptyStateProps> = (props) => {
    
    const {message, icon} = props;

    return (
        <div className={classes.EmptyStateSection}>
            {icon}
            <span className={classes.EmptyStateMessage}>
                {message}
            </span>
        </div>
    );
};

export default emptyState;

