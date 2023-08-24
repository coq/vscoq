import { ReactElement, ReactFragment } from 'react';
import { PpString } from '../types';

enum PpMode { vertical,  horizontal }

const fragmentOfPpStringWithMode = (pp:PpString, mode: PpMode, classes:CSSModuleClasses) : ReactFragment => {
    switch (pp[0]) {
        case "Ppcmd_empty":
            return <></>;
        case "Ppcmd_string":
            return pp[1];
        case "Ppcmd_glue":
            return pp[1].map(pp => fragmentOfPpStringWithMode(pp, mode, classes));
        case "Ppcmd_box":
          switch (pp[1][0]) {
              case "Pp_hbox":
                  mode = PpMode.horizontal;
                  break;
              case "Pp_vbox":
                  mode = PpMode.vertical;
                  break;
              case "Pp_hvbox":
                  mode = PpMode.horizontal; // TODO proper support for hvbox
                  break;
              case "Pp_hovbox":
                  mode = PpMode.horizontal; // TODO proper support for hovbox
                  break;
          };
          return fragmentOfPpStringWithMode(pp[2], mode, classes);
        case "Ppcmd_tag":
            return <span className={classes[pp[1].replaceAll(".", "-")]}>{fragmentOfPpStringWithMode(pp[2], mode, classes)}</span>;
        case "Ppcmd_print_break":
            switch (mode) {
                case PpMode.horizontal:
                    return " ".repeat(pp[1]);
                case PpMode.vertical:
                    return <br/>;
            }
        case "Ppcmd_force_newline":
            return <br/>;
        case "Ppcmd_comment":
            return pp[1];
    }
};

export const fragmentOfPpString = (pp:PpString, classes:CSSModuleClasses) : ReactFragment => {
    return fragmentOfPpStringWithMode(pp, PpMode.horizontal, classes);
};