import React, {FunctionComponent} from 'react';

import classes from './ResultName.module.css';

type ResultNameProps = {
    name: string; 
};

const resultName: FunctionComponent<ResultNameProps> = (props) => {
    
    const {name} = props;
    
    return <span className={classes.ResultName}> {name} </span>;
    
};

export default resultName;