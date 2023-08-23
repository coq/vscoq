import React, {FunctionComponent} from 'react';

import { fragmentOfPpString } from '../../utilities/pp';
import { PpString } from '../../types';

import classes from './ResultName.module.css';

type ResultNameProps = {
    name: PpString; 
};

const resultName: FunctionComponent<ResultNameProps> = (props) => {
    
    const {name} = props;
    
    return <>{fragmentOfPpString(name, classes)}</>;
    
};

export default resultName;