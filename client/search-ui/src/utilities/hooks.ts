import React, {useState, useEffect, useRef, useCallback} from 'react';

type BasicStateAction<S> = ((s:S) => S) | S;

export function useStateCallback<T>(
    initialState: (() => T) | T
  ): [T, (state: BasicStateAction<T>, cb?: (state: T) => void) => void] {
    const [state, setState] = useState(initialState);
    const cbRef = useRef<((state: T) => void) | undefined>(undefined); // init mutable ref container for callbacks

    const setStateCallback = useCallback(
        (state: BasicStateAction<T>, cb?: (state: T) => void) => {
            cbRef.current = cb; // store current, passed callback in ref
            setState(state);
        }, 
        []
    ); // keep object reference stable, exactly like `useState`

    useEffect(() => {
      // cb.current is `undefined` on initial render,
      // so we only invoke callback on state *updates*
      if (cbRef.current) {
        cbRef.current(state);
        cbRef.current = undefined; // reset callback after execution
      }
    }, [state]);

    return [state, setStateCallback];
};