{ fetchurl, fetchgit, linkFarm, runCommand, gnutar }: rec {
  offline_cache = linkFarm "offline" packages;
  packages = [
    {
      name = "https___registry.npmjs.org__ampproject_remapping___remapping_2.2.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__ampproject_remapping___remapping_2.2.0.tgz";
        url  = "https://registry.npmjs.org/@ampproject/remapping/-/remapping-2.2.0.tgz";
        sha512 = "qRmjj8nj9qmLTQXXmaR1cck3UXSRMPrbsLJAasZpF+t3riI71BXed5ebIOYwQntykeZuhjsdweEc9BxH5Jc26w==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_code_frame___code_frame_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_code_frame___code_frame_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/code-frame/-/code-frame-7.18.6.tgz";
        sha512 = "TDCmlK5eOvH+eH7cdAFlNXeVJqWIQ7gW9tY1GJIpUtFb6CmjVyq2VM3u71bOyR8CRihcCgMUYoDNyLXao3+70Q==";
      };
    }
    {
      name = "_babel_code_frame___code_frame_7.22.13.tgz";
      path = fetchurl {
        name = "_babel_code_frame___code_frame_7.22.13.tgz";
        url  = "https://registry.yarnpkg.com/@babel/code-frame/-/code-frame-7.22.13.tgz";
        sha512 = "XktuhWlJ5g+3TJXc5upd9Ks1HutSArik6jf2eAjYFyIOf4ej3RN+184cZbzDvbPnuTJIUhPKKJE3cIsYTiAT3w==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_compat_data___compat_data_7.20.10.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_compat_data___compat_data_7.20.10.tgz";
        url  = "https://registry.npmjs.org/@babel/compat-data/-/compat-data-7.20.10.tgz";
        sha512 = "sEnuDPpOJR/fcafHMjpcpGN5M2jbUGUHwmuWKM/YdPzeEDJg8bgmbcWQFUfE32MQjti1koACvoPVsDe8Uq+idg==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_core___core_7.20.12.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_core___core_7.20.12.tgz";
        url  = "https://registry.npmjs.org/@babel/core/-/core-7.20.12.tgz";
        sha512 = "XsMfHovsUYHFMdrIHkZphTN/2Hzzi78R08NuHfDBehym2VsPDL6Zn/JAD/JQdnRvbSsbQc4mVaU1m6JgtTEElg==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_generator___generator_7.20.7.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_generator___generator_7.20.7.tgz";
        url  = "https://registry.npmjs.org/@babel/generator/-/generator-7.20.7.tgz";
        sha512 = "7wqMOJq8doJMZmP4ApXTzLxSr7+oO2jroJURrVEp6XShrQUObV8Tq/D0NCcoYg2uHqUrjzO0zwBjoYzelxK+sw==";
      };
    }
    {
      name = "_babel_generator___generator_7.23.0.tgz";
      path = fetchurl {
        name = "_babel_generator___generator_7.23.0.tgz";
        url  = "https://registry.yarnpkg.com/@babel/generator/-/generator-7.23.0.tgz";
        sha512 = "lN85QRR+5IbYrMWM6Y4pE/noaQtg4pNiqeNGX60eqOfo6gtEj6uw/JagelB8vVztSd7R6M5n1+PQkDbHbBRU4g==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_annotate_as_pure___helper_annotate_as_pure_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_annotate_as_pure___helper_annotate_as_pure_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-annotate-as-pure/-/helper-annotate-as-pure-7.18.6.tgz";
        sha512 = "duORpUiYrEpzKIop6iNbjnwKLAKnJ47csTyRACyEmWj0QdUrm5aqNJGHSSEQSUAvNW0ojX0dOmK9dZduvkfeXA==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_compilation_targets___helper_compilation_targets_7.20.7.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_compilation_targets___helper_compilation_targets_7.20.7.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-compilation-targets/-/helper-compilation-targets-7.20.7.tgz";
        sha512 = "4tGORmfQcrc+bvrjb5y3dG9Mx1IOZjsHqQVUz7XCNHO+iTmqxWnVg3KRygjGmpRLJGdQSKuvFinbIb0CnZwHAQ==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_environment_visitor___helper_environment_visitor_7.18.9.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_environment_visitor___helper_environment_visitor_7.18.9.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-environment-visitor/-/helper-environment-visitor-7.18.9.tgz";
        sha512 = "3r/aACDJ3fhQ/EVgFy0hpj8oHyHpQc+LPtJoY9SzTThAsStm4Ptegq92vqKoE3vD706ZVFWITnMnxucw+S9Ipg==";
      };
    }
    {
      name = "_babel_helper_environment_visitor___helper_environment_visitor_7.22.20.tgz";
      path = fetchurl {
        name = "_babel_helper_environment_visitor___helper_environment_visitor_7.22.20.tgz";
        url  = "https://registry.yarnpkg.com/@babel/helper-environment-visitor/-/helper-environment-visitor-7.22.20.tgz";
        sha512 = "zfedSIzFhat/gFhWfHtgWvlec0nqB9YEIVrpuwjruLlXfUSnA8cJB0miHKwqDnQ7d32aKo2xt88/xZptwxbfhA==";
      };
    }
    {
      name = "_babel_helper_function_name___helper_function_name_7.23.0.tgz";
      path = fetchurl {
        name = "_babel_helper_function_name___helper_function_name_7.23.0.tgz";
        url  = "https://registry.yarnpkg.com/@babel/helper-function-name/-/helper-function-name-7.23.0.tgz";
        sha512 = "OErEqsrxjZTJciZ4Oo+eoZqeW9UIiOcuYKRJA4ZAgV9myA+pOXhhmpfNCKjEH/auVfEYVFJ6y1Tc4r0eIApqiw==";
      };
    }
    {
      name = "_babel_helper_hoist_variables___helper_hoist_variables_7.22.5.tgz";
      path = fetchurl {
        name = "_babel_helper_hoist_variables___helper_hoist_variables_7.22.5.tgz";
        url  = "https://registry.yarnpkg.com/@babel/helper-hoist-variables/-/helper-hoist-variables-7.22.5.tgz";
        sha512 = "wGjk9QZVzvknA6yKIUURb8zY3grXCcOZt+/7Wcy8O2uctxhplmUPkOdlgoNhmdVee2c92JXbf1xpMtVNbfoxRw==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_module_imports___helper_module_imports_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_module_imports___helper_module_imports_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-module-imports/-/helper-module-imports-7.18.6.tgz";
        sha512 = "0NFvs3VkuSYbFi1x2Vd6tKrywq+z/cLeYC/RJNFrIX/30Bf5aiGYbtvGXolEktzJH8o5E5KJ3tT+nkxuuZFVlA==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_module_transforms___helper_module_transforms_7.20.11.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_module_transforms___helper_module_transforms_7.20.11.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-module-transforms/-/helper-module-transforms-7.20.11.tgz";
        sha512 = "uRy78kN4psmji1s2QtbtcCSaj/LILFDp0f/ymhpQH5QY3nljUZCaNWz9X1dEj/8MBdBEFECs7yRhKn8i7NjZgg==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_plugin_utils___helper_plugin_utils_7.20.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_plugin_utils___helper_plugin_utils_7.20.2.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-plugin-utils/-/helper-plugin-utils-7.20.2.tgz";
        sha512 = "8RvlJG2mj4huQ4pZ+rU9lqKi9ZKiRmuvGuM2HlWmkmgOhbs6zEAw6IEiJ5cQqGbDzGZOhwuOQNtZMi/ENLjZoQ==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_simple_access___helper_simple_access_7.20.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_simple_access___helper_simple_access_7.20.2.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-simple-access/-/helper-simple-access-7.20.2.tgz";
        sha512 = "+0woI/WPq59IrqDYbVGfshjT5Dmk/nnbdpcF8SnMhhXObpTq2KNBdLFRFrkVdbDOyUmHBCxzm5FHV1rACIkIbA==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_split_export_declaration___helper_split_export_declaration_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_split_export_declaration___helper_split_export_declaration_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-split-export-declaration/-/helper-split-export-declaration-7.18.6.tgz";
        sha512 = "bde1etTx6ZyTmobl9LLMMQsaizFVZrquTEHOqKeQESMKo4PlObf+8+JA25ZsIpZhT/WEd39+vOdLXAFG/nELpA==";
      };
    }
    {
      name = "_babel_helper_split_export_declaration___helper_split_export_declaration_7.22.6.tgz";
      path = fetchurl {
        name = "_babel_helper_split_export_declaration___helper_split_export_declaration_7.22.6.tgz";
        url  = "https://registry.yarnpkg.com/@babel/helper-split-export-declaration/-/helper-split-export-declaration-7.22.6.tgz";
        sha512 = "AsUnxuLhRYsisFiaJwvp1QF+I3KjD5FOxut14q/GzovUe6orHLesW2C7d754kRm53h5gqrz6sFl6sxc4BVtE/g==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_string_parser___helper_string_parser_7.19.4.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_string_parser___helper_string_parser_7.19.4.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-string-parser/-/helper-string-parser-7.19.4.tgz";
        sha512 = "nHtDoQcuqFmwYNYPz3Rah5ph2p8PFeFCsZk9A/48dPc/rGocJ5J3hAAZ7pb76VWX3fZKu+uEr/FhH5jLx7umrw==";
      };
    }
    {
      name = "_babel_helper_string_parser___helper_string_parser_7.22.5.tgz";
      path = fetchurl {
        name = "_babel_helper_string_parser___helper_string_parser_7.22.5.tgz";
        url  = "https://registry.yarnpkg.com/@babel/helper-string-parser/-/helper-string-parser-7.22.5.tgz";
        sha512 = "mM4COjgZox8U+JcXQwPijIZLElkgEpO5rsERVDJTc2qfCDfERyob6k5WegS14SX18IIjv+XD+GrqNumY5JRCDw==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_validator_identifier___helper_validator_identifier_7.19.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_validator_identifier___helper_validator_identifier_7.19.1.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-validator-identifier/-/helper-validator-identifier-7.19.1.tgz";
        sha512 = "awrNfaMtnHUr653GgGEs++LlAvW6w+DcPrOliSMXWCKo597CwL5Acf/wWdNkf/tfEQE3mjkeD1YOVZOUV/od1w==";
      };
    }
    {
      name = "_babel_helper_validator_identifier___helper_validator_identifier_7.22.20.tgz";
      path = fetchurl {
        name = "_babel_helper_validator_identifier___helper_validator_identifier_7.22.20.tgz";
        url  = "https://registry.yarnpkg.com/@babel/helper-validator-identifier/-/helper-validator-identifier-7.22.20.tgz";
        sha512 = "Y4OZ+ytlatR8AI+8KZfKuL5urKp7qey08ha31L8b3BwewJAoJamTzyvxPR/5D+KkdJCGPq/+8TukHBlY10FX9A==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helper_validator_option___helper_validator_option_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helper_validator_option___helper_validator_option_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/helper-validator-option/-/helper-validator-option-7.18.6.tgz";
        sha512 = "XO7gESt5ouv/LRJdrVjkShckw6STTaB7l9BrpBaAHDeF5YZT+01PCwmR0SJHnkW6i8OwW/EVWRShfi4j2x+KQw==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_helpers___helpers_7.20.13.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_helpers___helpers_7.20.13.tgz";
        url  = "https://registry.npmjs.org/@babel/helpers/-/helpers-7.20.13.tgz";
        sha512 = "nzJ0DWCL3gB5RCXbUO3KIMMsBY2Eqbx8mBpKGE/02PgyRQFcPQLbkQ1vyy596mZLaP+dAfD+R4ckASzNVmW3jg==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_highlight___highlight_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_highlight___highlight_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/highlight/-/highlight-7.18.6.tgz";
        sha512 = "u7stbOuYjaPezCuLj29hNW1v64M2Md2qupEKP1fHc7WdOA3DgLh37suiSrZYY7haUB7iBeQZ9P1uiRF359do3g==";
      };
    }
    {
      name = "_babel_highlight___highlight_7.22.20.tgz";
      path = fetchurl {
        name = "_babel_highlight___highlight_7.22.20.tgz";
        url  = "https://registry.yarnpkg.com/@babel/highlight/-/highlight-7.22.20.tgz";
        sha512 = "dkdMCN3py0+ksCgYmGG8jKeGA/8Tk+gJwSYYlFGxG5lmhfKNoAy004YpLxpS1W2J8m/EK2Ew+yOs9pVRwO89mg==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_parser___parser_7.20.13.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_parser___parser_7.20.13.tgz";
        url  = "https://registry.npmjs.org/@babel/parser/-/parser-7.20.13.tgz";
        sha512 = "gFDLKMfpiXCsjt4za2JA9oTMn70CeseCehb11kRZgvd7+F67Hih3OHOK24cRrWECJ/ljfPGac6ygXAs/C8kIvw==";
      };
    }
    {
      name = "_babel_parser___parser_7.23.0.tgz";
      path = fetchurl {
        name = "_babel_parser___parser_7.23.0.tgz";
        url  = "https://registry.yarnpkg.com/@babel/parser/-/parser-7.23.0.tgz";
        sha512 = "vvPKKdMemU85V9WE/l5wZEmImpCtLqbnTvqDS2U1fJ96KrxoW7KrXhNsNCblQlg8Ck4b85yxdTyelsMUgFUXiw==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_plugin_syntax_jsx___plugin_syntax_jsx_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_plugin_syntax_jsx___plugin_syntax_jsx_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/plugin-syntax-jsx/-/plugin-syntax-jsx-7.18.6.tgz";
        sha512 = "6mmljtAedFGTWu2p/8WIORGwy+61PLgOMPOdazc7YoJ9ZCWUyFy3A6CpPkRKLKD1ToAesxX8KGEViAiLo9N+7Q==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_plugin_transform_react_jsx_development___plugin_transform_react_jsx_development_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_plugin_transform_react_jsx_development___plugin_transform_react_jsx_development_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/plugin-transform-react-jsx-development/-/plugin-transform-react-jsx-development-7.18.6.tgz";
        sha512 = "SA6HEjwYFKF7WDjWcMcMGUimmw/nhNRDWxr+KaLSCrkD/LMDBvWRmHAYgE1HDeF8KUuI8OAu+RT6EOtKxSW2qA==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_plugin_transform_react_jsx_self___plugin_transform_react_jsx_self_7.18.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_plugin_transform_react_jsx_self___plugin_transform_react_jsx_self_7.18.6.tgz";
        url  = "https://registry.npmjs.org/@babel/plugin-transform-react-jsx-self/-/plugin-transform-react-jsx-self-7.18.6.tgz";
        sha512 = "A0LQGx4+4Jv7u/tWzoJF7alZwnBDQd6cGLh9P+Ttk4dpiL+J5p7NSNv/9tlEFFJDq3kjxOavWmbm6t0Gk+A3Ig==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_plugin_transform_react_jsx_source___plugin_transform_react_jsx_source_7.19.6.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_plugin_transform_react_jsx_source___plugin_transform_react_jsx_source_7.19.6.tgz";
        url  = "https://registry.npmjs.org/@babel/plugin-transform-react-jsx-source/-/plugin-transform-react-jsx-source-7.19.6.tgz";
        sha512 = "RpAi004QyMNisst/pvSanoRdJ4q+jMCWyk9zdw/CyLB9j8RXEahodR6l2GyttDRyEVWZtbN+TpLiHJ3t34LbsQ==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_plugin_transform_react_jsx___plugin_transform_react_jsx_7.20.13.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_plugin_transform_react_jsx___plugin_transform_react_jsx_7.20.13.tgz";
        url  = "https://registry.npmjs.org/@babel/plugin-transform-react-jsx/-/plugin-transform-react-jsx-7.20.13.tgz";
        sha512 = "MmTZx/bkUrfJhhYAYt3Urjm+h8DQGrPrnKQ94jLo7NLuOU+T89a7IByhKmrb8SKhrIYIQ0FN0CHMbnFRen4qNw==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_template___template_7.20.7.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_template___template_7.20.7.tgz";
        url  = "https://registry.npmjs.org/@babel/template/-/template-7.20.7.tgz";
        sha512 = "8SegXApWe6VoNw0r9JHpSteLKTpTiLZ4rMlGIm9JQ18KiCtyQiAMEazujAHrUS5flrcqYZa75ukev3P6QmUwUw==";
      };
    }
    {
      name = "_babel_template___template_7.22.15.tgz";
      path = fetchurl {
        name = "_babel_template___template_7.22.15.tgz";
        url  = "https://registry.yarnpkg.com/@babel/template/-/template-7.22.15.tgz";
        sha512 = "QPErUVm4uyJa60rkI73qneDacvdvzxshT3kksGqlGWYdOTIUOwJ7RDUL8sGqslY1uXWSL6xMFKEXDS3ox2uF0w==";
      };
    }
    {
      name = "_babel_traverse___traverse_7.23.2.tgz";
      path = fetchurl {
        name = "_babel_traverse___traverse_7.23.2.tgz";
        url  = "https://registry.yarnpkg.com/@babel/traverse/-/traverse-7.23.2.tgz";
        sha512 = "azpe59SQ48qG6nu2CzcMLbxUudtN+dOM9kDbUqGq3HXUJRlo7i8fvPoxQUzYgLZ4cMVmuZgm8vvBpNeRhd6XSw==";
      };
    }
    {
      name = "https___registry.npmjs.org__babel_types___types_7.20.7.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__babel_types___types_7.20.7.tgz";
        url  = "https://registry.npmjs.org/@babel/types/-/types-7.20.7.tgz";
        sha512 = "69OnhBxSSgK0OzTJai4kyPDiKTIe3j+ctaHdIGVbRahTLAT7L3R9oeXHC2aVSuGYt3cVnoAMDmOCgJ2yaiLMvg==";
      };
    }
    {
      name = "_babel_types___types_7.23.0.tgz";
      path = fetchurl {
        name = "_babel_types___types_7.23.0.tgz";
        url  = "https://registry.yarnpkg.com/@babel/types/-/types-7.23.0.tgz";
        sha512 = "0oIyUfKoI3mSqMvsxBdclDwxXKXAUA8v/apZbc+iSyARYou1o8ZGDxbUYyLFoW2arqS2jDGqJuZvv1d/io1axg==";
      };
    }
    {
      name = "_esbuild_linux_loong64___linux_loong64_0.14.54.tgz";
      path = fetchurl {
        name = "_esbuild_linux_loong64___linux_loong64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/@esbuild/linux-loong64/-/linux-loong64-0.14.54.tgz";
        sha512 = "bZBrLAIX1kpWelV0XemxBZllyRmM6vgFQQG2GdNb+r3Fkp0FOh1NJSvekXDs7jq70k4euu1cryLMfU+mTXlEpw==";
      };
    }
    {
      name = "https___registry.npmjs.org__jridgewell_gen_mapping___gen_mapping_0.1.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__jridgewell_gen_mapping___gen_mapping_0.1.1.tgz";
        url  = "https://registry.npmjs.org/@jridgewell/gen-mapping/-/gen-mapping-0.1.1.tgz";
        sha512 = "sQXCasFk+U8lWYEe66WxRDOE9PjVz4vSM51fTu3Hw+ClTpUSQb718772vH3pyS5pShp6lvQM7SxgIDXXXmOX7w==";
      };
    }
    {
      name = "https___registry.npmjs.org__jridgewell_gen_mapping___gen_mapping_0.3.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__jridgewell_gen_mapping___gen_mapping_0.3.2.tgz";
        url  = "https://registry.npmjs.org/@jridgewell/gen-mapping/-/gen-mapping-0.3.2.tgz";
        sha512 = "mh65xKQAzI6iBcFzwv28KVWSmCkdRBWoOh+bYQGW3+6OZvbbN3TqMGo5hqYxQniRcH9F2VZIoJCm4pa3BPDK/A==";
      };
    }
    {
      name = "https___registry.npmjs.org__jridgewell_resolve_uri___resolve_uri_3.1.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__jridgewell_resolve_uri___resolve_uri_3.1.0.tgz";
        url  = "https://registry.npmjs.org/@jridgewell/resolve-uri/-/resolve-uri-3.1.0.tgz";
        sha512 = "F2msla3tad+Mfht5cJq7LSXcdudKTWCVYUgw6pLFOOHSTtZlj6SWNYAp+AhuqLmWdBO2X5hPrLcu8cVP8fy28w==";
      };
    }
    {
      name = "_jridgewell_resolve_uri___resolve_uri_3.1.1.tgz";
      path = fetchurl {
        name = "_jridgewell_resolve_uri___resolve_uri_3.1.1.tgz";
        url  = "https://registry.yarnpkg.com/@jridgewell/resolve-uri/-/resolve-uri-3.1.1.tgz";
        sha512 = "dSYZh7HhCDtCKm4QakX0xFpsRDqjjtZf/kjI/v3T3Nwt5r8/qz/M19F9ySyOqU94SXBmeG9ttTul+YnR4LOxFA==";
      };
    }
    {
      name = "https___registry.npmjs.org__jridgewell_set_array___set_array_1.1.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__jridgewell_set_array___set_array_1.1.2.tgz";
        url  = "https://registry.npmjs.org/@jridgewell/set-array/-/set-array-1.1.2.tgz";
        sha512 = "xnkseuNADM0gt2bs+BvhO0p78Mk762YnZdsuzFV018NoG1Sj1SCQvpSqa7XUaTam5vAGasABV9qXASMKnFMwMw==";
      };
    }
    {
      name = "https___registry.npmjs.org__jridgewell_sourcemap_codec___sourcemap_codec_1.4.14.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__jridgewell_sourcemap_codec___sourcemap_codec_1.4.14.tgz";
        url  = "https://registry.npmjs.org/@jridgewell/sourcemap-codec/-/sourcemap-codec-1.4.14.tgz";
        sha512 = "XPSJHWmi394fuUuzDnGz1wiKqWfo1yXecHQMRf2l6hztTO+nPru658AyDngaBe7isIxEkRsPR3FZh+s7iVa4Uw==";
      };
    }
    {
      name = "_jridgewell_sourcemap_codec___sourcemap_codec_1.4.15.tgz";
      path = fetchurl {
        name = "_jridgewell_sourcemap_codec___sourcemap_codec_1.4.15.tgz";
        url  = "https://registry.yarnpkg.com/@jridgewell/sourcemap-codec/-/sourcemap-codec-1.4.15.tgz";
        sha512 = "eF2rxCRulEKXHTRiDrDy6erMYWqNw4LPdQ8UQA4huuxaQsVeRPFl2oM8oDGxMFhJUWZf9McpLtJasDDZb/Bpeg==";
      };
    }
    {
      name = "_jridgewell_trace_mapping___trace_mapping_0.3.20.tgz";
      path = fetchurl {
        name = "_jridgewell_trace_mapping___trace_mapping_0.3.20.tgz";
        url  = "https://registry.yarnpkg.com/@jridgewell/trace-mapping/-/trace-mapping-0.3.20.tgz";
        sha512 = "R8LcPeWZol2zR8mmH3JeKQ6QRCFb7XgUhV9ZlGhHLGyg4wpPiPZNQOOWhFZhxKw8u//yTbNGI42Bx/3paXEQ+Q==";
      };
    }
    {
      name = "https___registry.npmjs.org__jridgewell_trace_mapping___trace_mapping_0.3.17.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__jridgewell_trace_mapping___trace_mapping_0.3.17.tgz";
        url  = "https://registry.npmjs.org/@jridgewell/trace-mapping/-/trace-mapping-0.3.17.tgz";
        sha512 = "MCNzAp77qzKca9+W/+I0+sEpaUnZoeasnghNeVc41VZCEKaCH73Vq3BZZ/SzWIgrqE4H4ceI+p+b6C0mHf9T4g==";
      };
    }
    {
      name = "_juggle_resize_observer___resize_observer_3.4.0.tgz";
      path = fetchurl {
        name = "_juggle_resize_observer___resize_observer_3.4.0.tgz";
        url  = "https://registry.yarnpkg.com/@juggle/resize-observer/-/resize-observer-3.4.0.tgz";
        sha512 = "dfLbk+PwWvFzSxwk3n5ySL0hfBog779o8h68wK/7/APo/7cgyWp5jcXockbxdk5kFRkbeXWm4Fbi9FrdN381sA==";
      };
    }
    {
      name = "https___registry.npmjs.org__microsoft_fast_element___fast_element_1.11.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__microsoft_fast_element___fast_element_1.11.0.tgz";
        url  = "https://registry.npmjs.org/@microsoft/fast-element/-/fast-element-1.11.0.tgz";
        sha512 = "VKJYMkS5zgzHHb66sY7AFpYv6IfFhXrjQcAyNgi2ivD65My1XOhtjfKez5ELcLFRJfgZNAxvI8kE69apXERTkw==";
      };
    }
    {
      name = "https___registry.npmjs.org__microsoft_fast_foundation___fast_foundation_2.47.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__microsoft_fast_foundation___fast_foundation_2.47.0.tgz";
        url  = "https://registry.npmjs.org/@microsoft/fast-foundation/-/fast-foundation-2.47.0.tgz";
        sha512 = "EyFuioaZQ9ngjUNRQi8R3dIPPsaNQdUOS+tP0G7b1MJRhXmQWIitBM6IeveQA6ZvXG6H21dqgrfEWlsYrUZ2sw==";
      };
    }
    {
      name = "https___registry.npmjs.org__microsoft_fast_react_wrapper___fast_react_wrapper_0.1.48.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__microsoft_fast_react_wrapper___fast_react_wrapper_0.1.48.tgz";
        url  = "https://registry.npmjs.org/@microsoft/fast-react-wrapper/-/fast-react-wrapper-0.1.48.tgz";
        sha512 = "9NvEjru9Kn5ZKjomAMX6v+eF0DR+eDkxKDwDfi+Wb73kTbrNzcnmlwd4diN15ygH97kldgj2+lpvI4CKLQQWLg==";
      };
    }
    {
      name = "https___registry.npmjs.org__microsoft_fast_web_utilities___fast_web_utilities_5.4.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__microsoft_fast_web_utilities___fast_web_utilities_5.4.1.tgz";
        url  = "https://registry.npmjs.org/@microsoft/fast-web-utilities/-/fast-web-utilities-5.4.1.tgz";
        sha512 = "ReWYncndjV3c8D8iq9tp7NcFNc1vbVHvcBFPME2nNFKNbS1XCesYZGlIlf3ot5EmuOXPlrzUHOWzQ2vFpIkqDg==";
      };
    }
    {
      name = "_react_hook_latest___latest_1.0.3.tgz";
      path = fetchurl {
        name = "_react_hook_latest___latest_1.0.3.tgz";
        url  = "https://registry.yarnpkg.com/@react-hook/latest/-/latest-1.0.3.tgz";
        sha512 = "dy6duzl+JnAZcDbNTfmaP3xHiKtbXYOaz3G51MGVljh548Y8MWzTr+PHLOfvpypEVW9zwvl+VyKjbWKEVbV1Rg==";
      };
    }
    {
      name = "_react_hook_passive_layout_effect___passive_layout_effect_1.2.1.tgz";
      path = fetchurl {
        name = "_react_hook_passive_layout_effect___passive_layout_effect_1.2.1.tgz";
        url  = "https://registry.yarnpkg.com/@react-hook/passive-layout-effect/-/passive-layout-effect-1.2.1.tgz";
        sha512 = "IwEphTD75liO8g+6taS+4oqz+nnroocNfWVHWz7j+N+ZO2vYrc6PV1q7GQhuahL0IOR7JccFTsFKQ/mb6iZWAg==";
      };
    }
    {
      name = "_react_hook_resize_observer___resize_observer_1.2.6.tgz";
      path = fetchurl {
        name = "_react_hook_resize_observer___resize_observer_1.2.6.tgz";
        url  = "https://registry.yarnpkg.com/@react-hook/resize-observer/-/resize-observer-1.2.6.tgz";
        sha512 = "DlBXtLSW0DqYYTW3Ft1/GQFZlTdKY5VAFIC4+km6IK5NiPPDFchGbEJm1j6pSgMqPRHbUQgHJX7RaR76ic1LWA==";
      };
    }
    {
      name = "https___registry.npmjs.org__rollup_pluginutils___pluginutils_4.2.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__rollup_pluginutils___pluginutils_4.2.1.tgz";
        url  = "https://registry.npmjs.org/@rollup/pluginutils/-/pluginutils-4.2.1.tgz";
        sha512 = "iKnFXr7NkdZAIHiIWE+BX5ULi/ucVFYWD6TbAV+rZctiRTY2PL6tsIKhoIOaoskiWAkgu+VsbXgUVDNLHf+InQ==";
      };
    }
    {
      name = "https___registry.npmjs.org__types_prop_types___prop_types_15.7.5.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__types_prop_types___prop_types_15.7.5.tgz";
        url  = "https://registry.npmjs.org/@types/prop-types/-/prop-types-15.7.5.tgz";
        sha512 = "JCB8C6SnDoQf0cNycqd/35A7MjcnK+ZTqE7judS6o7utxUCg6imJg3QK2qzHKszlTjcj2cn+NwMB2i96ubpj7w==";
      };
    }
    {
      name = "https___registry.npmjs.org__types_react_dom___react_dom_17.0.18.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__types_react_dom___react_dom_17.0.18.tgz";
        url  = "https://registry.npmjs.org/@types/react-dom/-/react-dom-17.0.18.tgz";
        sha512 = "rLVtIfbwyur2iFKykP2w0pl/1unw26b5td16d5xMgp7/yjTHomkyxPYChFoCr/FtEX1lN9wY6lFj1qvKdS5kDw==";
      };
    }
    {
      name = "https___registry.npmjs.org__types_react___react_17.0.53.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__types_react___react_17.0.53.tgz";
        url  = "https://registry.npmjs.org/@types/react/-/react-17.0.53.tgz";
        sha512 = "1yIpQR2zdYu1Z/dc1OxC+MA6GR240u3gcnP4l6mvj/PJiVaqHsQPmWttsvHsfnhfPbU2FuGmo0wSITPygjBmsw==";
      };
    }
    {
      name = "https___registry.npmjs.org__types_scheduler___scheduler_0.16.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__types_scheduler___scheduler_0.16.2.tgz";
        url  = "https://registry.npmjs.org/@types/scheduler/-/scheduler-0.16.2.tgz";
        sha512 = "hppQEBDmlwhFAXKJX2KnWLYu5yMfi91yazPb2l+lbJiwW+wdo1gNeRA+3RgNSO39WYX2euey41KEwnqesU2Jew==";
      };
    }
    {
      name = "_types_uuid___uuid_8.3.4.tgz";
      path = fetchurl {
        name = "_types_uuid___uuid_8.3.4.tgz";
        url  = "https://registry.yarnpkg.com/@types/uuid/-/uuid-8.3.4.tgz";
        sha512 = "c/I8ZRb51j+pYGAu5CrFMRxqZ2ke4y2grEBO5AUjgSkSk+qT2Ea+OdWElz/OiMf5MNpn2b17kuVBwZLQJXzihw==";
      };
    }
    {
      name = "https___registry.npmjs.org__types_vscode_webview___vscode_webview_1.57.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__types_vscode_webview___vscode_webview_1.57.1.tgz";
        url  = "https://registry.npmjs.org/@types/vscode-webview/-/vscode-webview-1.57.1.tgz";
        sha512 = "ghW5SfuDmsGDS2A4xkvGsLwDRNc3Vj5rS6rPOyPm/IryZuf3wceZKxgYaUoW+k9f0f/CB7y2c1rRsdOWZWn0PQ==";
      };
    }
    {
      name = "https___registry.npmjs.org__vitejs_plugin_react___plugin_react_1.3.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__vitejs_plugin_react___plugin_react_1.3.2.tgz";
        url  = "https://registry.npmjs.org/@vitejs/plugin-react/-/plugin-react-1.3.2.tgz";
        sha512 = "aurBNmMo0kz1O4qRoY+FM4epSA39y3ShWGuqfLRA/3z0oEJAdtoSfgA3aO98/PCCHAqMaduLxIxErWrVKIFzXA==";
      };
    }
    {
      name = "https___registry.npmjs.org__vscode_codicons___codicons_0.0.32.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__vscode_codicons___codicons_0.0.32.tgz";
        url  = "https://registry.npmjs.org/@vscode/codicons/-/codicons-0.0.32.tgz";
        sha512 = "3lgSTWhAzzWN/EPURoY4ZDBEA80OPmnaknNujA3qnI4Iu7AONWd9xF3iE4L+4prIe8E3TUnLQ4pxoaFTEEZNwg==";
      };
    }
    {
      name = "https___registry.npmjs.org__vscode_webview_ui_toolkit___webview_ui_toolkit_1.2.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org__vscode_webview_ui_toolkit___webview_ui_toolkit_1.2.1.tgz";
        url  = "https://registry.npmjs.org/@vscode/webview-ui-toolkit/-/webview-ui-toolkit-1.2.1.tgz";
        sha512 = "ZpVqLxoFWWk8mmAN7jr1v9yjD6NGBIoflAedNSusmaViqwHZ2znKBwAwcumLOlNlqmST6QMkiTVys7O8rzfd0w==";
      };
    }
    {
      name = "https___registry.npmjs.org_ansi_styles___ansi_styles_3.2.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_ansi_styles___ansi_styles_3.2.1.tgz";
        url  = "https://registry.npmjs.org/ansi-styles/-/ansi-styles-3.2.1.tgz";
        sha512 = "VT0ZI6kZRdTh8YyJw3SMbYm/u+NqfsAxEpWO0Pf9sq8/e94WxxOpPKx9FR1FlyCtOVDNOQ+8ntlqFxiRc+r5qA==";
      };
    }
    {
      name = "https___registry.npmjs.org_browserslist___browserslist_4.21.4.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_browserslist___browserslist_4.21.4.tgz";
        url  = "https://registry.npmjs.org/browserslist/-/browserslist-4.21.4.tgz";
        sha512 = "CBHJJdDmgjl3daYjN5Cp5kbTf1mUhZoS+beLklHIvkOWscs83YAhLlF3Wsh/lciQYAcbBJgTOD44VtG31ZM4Hw==";
      };
    }
    {
      name = "https___registry.npmjs.org_caniuse_lite___caniuse_lite_1.0.30001447.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_caniuse_lite___caniuse_lite_1.0.30001447.tgz";
        url  = "https://registry.npmjs.org/caniuse-lite/-/caniuse-lite-1.0.30001447.tgz";
        sha512 = "bdKU1BQDPeEXe9A39xJnGtY0uRq/z5osrnXUw0TcK+EYno45Y+U7QU9HhHEyzvMDffpYadFXi3idnSNkcwLkTw==";
      };
    }
    {
      name = "https___registry.npmjs.org_chalk___chalk_2.4.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_chalk___chalk_2.4.2.tgz";
        url  = "https://registry.npmjs.org/chalk/-/chalk-2.4.2.tgz";
        sha512 = "Mti+f9lpJNcwF4tWV8/OrTTtF1gZi+f8FqlyAdouralcFWFQWF2+NgCHShjkCb+IFBLq9buZwE1xckQU4peSuQ==";
      };
    }
    {
      name = "https___registry.npmjs.org_color_convert___color_convert_1.9.3.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_color_convert___color_convert_1.9.3.tgz";
        url  = "https://registry.npmjs.org/color-convert/-/color-convert-1.9.3.tgz";
        sha512 = "QfAUtd+vFdAtFQcC8CCyYt1fYWxSqAiK2cSD6zDB8N3cpsEBAvRxp9zOGg6G/SHHJYAT88/az/IuDGALsNVbGg==";
      };
    }
    {
      name = "https___registry.npmjs.org_color_name___color_name_1.1.3.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_color_name___color_name_1.1.3.tgz";
        url  = "https://registry.npmjs.org/color-name/-/color-name-1.1.3.tgz";
        sha512 = "72fSenhMw2HZMTVHeCA9KCmpEIbzWiQsjN+BHcBbS9vr1mtt+vJjPdksIBNUmKAW8TFUDPJK5SUU3QhE9NEXDw==";
      };
    }
    {
      name = "https___registry.npmjs.org_convert_source_map___convert_source_map_1.9.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_convert_source_map___convert_source_map_1.9.0.tgz";
        url  = "https://registry.npmjs.org/convert-source-map/-/convert-source-map-1.9.0.tgz";
        sha512 = "ASFBup0Mz1uyiIjANan1jzLQami9z1PoYSZCiiYW2FczPbenXc45FZdBZLzOT+r6+iciuEModtmCti+hjaAk0A==";
      };
    }
    {
      name = "https___registry.npmjs.org_csstype___csstype_3.1.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_csstype___csstype_3.1.1.tgz";
        url  = "https://registry.npmjs.org/csstype/-/csstype-3.1.1.tgz";
        sha512 = "DJR/VvkAvSZW9bTouZue2sSxDwdTN92uHjqeKVm+0dAqdfNykRzQ95tay8aXMBAAPpUiq4Qcug2L7neoRh2Egw==";
      };
    }
    {
      name = "https___registry.npmjs.org_debug___debug_4.3.4.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_debug___debug_4.3.4.tgz";
        url  = "https://registry.npmjs.org/debug/-/debug-4.3.4.tgz";
        sha512 = "PRWFHuSU3eDtQJPvnNY7Jcket1j0t5OuOsFzPPzsekD52Zl8qUfFIPEiswXqIvHWGVHOgX+7G/vCNNhehwxfkQ==";
      };
    }
    {
      name = "https___registry.npmjs.org_electron_to_chromium___electron_to_chromium_1.4.284.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_electron_to_chromium___electron_to_chromium_1.4.284.tgz";
        url  = "https://registry.npmjs.org/electron-to-chromium/-/electron-to-chromium-1.4.284.tgz";
        sha512 = "M8WEXFuKXMYMVr45fo8mq0wUrrJHheiKZf6BArTKk9ZBYCKJEOU5H8cdWgDT+qCVZf7Na4lVUaZsA+h6uA9+PA==";
      };
    }
    {
      name = "esbuild_android_64___esbuild_android_64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_android_64___esbuild_android_64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-android-64/-/esbuild-android-64-0.14.54.tgz";
        sha512 = "Tz2++Aqqz0rJ7kYBfz+iqyE3QMycD4vk7LBRyWaAVFgFtQ/O8EJOnVmTOiDWYZ/uYzB4kvP+bqejYdVKzE5lAQ==";
      };
    }
    {
      name = "esbuild_android_arm64___esbuild_android_arm64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_android_arm64___esbuild_android_arm64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-android-arm64/-/esbuild-android-arm64-0.14.54.tgz";
        sha512 = "F9E+/QDi9sSkLaClO8SOV6etqPd+5DgJje1F9lOWoNncDdOBL2YF59IhsWATSt0TLZbYCf3pNlTHvVV5VfHdvg==";
      };
    }
    {
      name = "esbuild_darwin_64___esbuild_darwin_64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_darwin_64___esbuild_darwin_64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-darwin-64/-/esbuild-darwin-64-0.14.54.tgz";
        sha512 = "jtdKWV3nBviOd5v4hOpkVmpxsBy90CGzebpbO9beiqUYVMBtSc0AL9zGftFuBon7PNDcdvNCEuQqw2x0wP9yug==";
      };
    }
    {
      name = "esbuild_darwin_arm64___esbuild_darwin_arm64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_darwin_arm64___esbuild_darwin_arm64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-darwin-arm64/-/esbuild-darwin-arm64-0.14.54.tgz";
        sha512 = "OPafJHD2oUPyvJMrsCvDGkRrVCar5aVyHfWGQzY1dWnzErjrDuSETxwA2HSsyg2jORLY8yBfzc1MIpUkXlctmw==";
      };
    }
    {
      name = "esbuild_freebsd_64___esbuild_freebsd_64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_freebsd_64___esbuild_freebsd_64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-freebsd-64/-/esbuild-freebsd-64-0.14.54.tgz";
        sha512 = "OKwd4gmwHqOTp4mOGZKe/XUlbDJ4Q9TjX0hMPIDBUWWu/kwhBAudJdBoxnjNf9ocIB6GN6CPowYpR/hRCbSYAg==";
      };
    }
    {
      name = "esbuild_freebsd_arm64___esbuild_freebsd_arm64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_freebsd_arm64___esbuild_freebsd_arm64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-freebsd-arm64/-/esbuild-freebsd-arm64-0.14.54.tgz";
        sha512 = "sFwueGr7OvIFiQT6WeG0jRLjkjdqWWSrfbVwZp8iMP+8UHEHRBvlaxL6IuKNDwAozNUmbb8nIMXa7oAOARGs1Q==";
      };
    }
    {
      name = "esbuild_linux_32___esbuild_linux_32_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_linux_32___esbuild_linux_32_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-linux-32/-/esbuild-linux-32-0.14.54.tgz";
        sha512 = "1ZuY+JDI//WmklKlBgJnglpUL1owm2OX+8E1syCD6UAxcMM/XoWd76OHSjl/0MR0LisSAXDqgjT3uJqT67O3qw==";
      };
    }
    {
      name = "https___registry.npmjs.org_esbuild_linux_64___esbuild_linux_64_0.14.54.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_esbuild_linux_64___esbuild_linux_64_0.14.54.tgz";
        url  = "https://registry.npmjs.org/esbuild-linux-64/-/esbuild-linux-64-0.14.54.tgz";
        sha512 = "EgjAgH5HwTbtNsTqQOXWApBaPVdDn7XcK+/PtJwZLT1UmpLoznPd8c5CxqsH2dQK3j05YsB3L17T8vE7cp4cCg==";
      };
    }
    {
      name = "esbuild_linux_arm64___esbuild_linux_arm64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_linux_arm64___esbuild_linux_arm64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-linux-arm64/-/esbuild-linux-arm64-0.14.54.tgz";
        sha512 = "WL71L+0Rwv+Gv/HTmxTEmpv0UgmxYa5ftZILVi2QmZBgX3q7+tDeOQNqGtdXSdsL8TQi1vIaVFHUPDe0O0kdig==";
      };
    }
    {
      name = "esbuild_linux_arm___esbuild_linux_arm_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_linux_arm___esbuild_linux_arm_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-linux-arm/-/esbuild-linux-arm-0.14.54.tgz";
        sha512 = "qqz/SjemQhVMTnvcLGoLOdFpCYbz4v4fUo+TfsWG+1aOu70/80RV6bgNpR2JCrppV2moUQkww+6bWxXRL9YMGw==";
      };
    }
    {
      name = "esbuild_linux_mips64le___esbuild_linux_mips64le_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_linux_mips64le___esbuild_linux_mips64le_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-linux-mips64le/-/esbuild-linux-mips64le-0.14.54.tgz";
        sha512 = "qTHGQB8D1etd0u1+sB6p0ikLKRVuCWhYQhAHRPkO+OF3I/iSlTKNNS0Lh2Oc0g0UFGguaFZZiPJdJey3AGpAlw==";
      };
    }
    {
      name = "esbuild_linux_ppc64le___esbuild_linux_ppc64le_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_linux_ppc64le___esbuild_linux_ppc64le_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-linux-ppc64le/-/esbuild-linux-ppc64le-0.14.54.tgz";
        sha512 = "j3OMlzHiqwZBDPRCDFKcx595XVfOfOnv68Ax3U4UKZ3MTYQB5Yz3X1mn5GnodEVYzhtZgxEBidLWeIs8FDSfrQ==";
      };
    }
    {
      name = "esbuild_linux_riscv64___esbuild_linux_riscv64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_linux_riscv64___esbuild_linux_riscv64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-linux-riscv64/-/esbuild-linux-riscv64-0.14.54.tgz";
        sha512 = "y7Vt7Wl9dkOGZjxQZnDAqqn+XOqFD7IMWiewY5SPlNlzMX39ocPQlOaoxvT4FllA5viyV26/QzHtvTjVNOxHZg==";
      };
    }
    {
      name = "esbuild_linux_s390x___esbuild_linux_s390x_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_linux_s390x___esbuild_linux_s390x_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-linux-s390x/-/esbuild-linux-s390x-0.14.54.tgz";
        sha512 = "zaHpW9dziAsi7lRcyV4r8dhfG1qBidQWUXweUjnw+lliChJqQr+6XD71K41oEIC3Mx1KStovEmlzm+MkGZHnHA==";
      };
    }
    {
      name = "esbuild_netbsd_64___esbuild_netbsd_64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_netbsd_64___esbuild_netbsd_64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-netbsd-64/-/esbuild-netbsd-64-0.14.54.tgz";
        sha512 = "PR01lmIMnfJTgeU9VJTDY9ZerDWVFIUzAtJuDHwwceppW7cQWjBBqP48NdeRtoP04/AtO9a7w3viI+PIDr6d+w==";
      };
    }
    {
      name = "esbuild_openbsd_64___esbuild_openbsd_64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_openbsd_64___esbuild_openbsd_64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-openbsd-64/-/esbuild-openbsd-64-0.14.54.tgz";
        sha512 = "Qyk7ikT2o7Wu76UsvvDS5q0amJvmRzDyVlL0qf5VLsLchjCa1+IAvd8kTBgUxD7VBUUVgItLkk609ZHUc1oCaw==";
      };
    }
    {
      name = "esbuild_sunos_64___esbuild_sunos_64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_sunos_64___esbuild_sunos_64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-sunos-64/-/esbuild-sunos-64-0.14.54.tgz";
        sha512 = "28GZ24KmMSeKi5ueWzMcco6EBHStL3B6ubM7M51RmPwXQGLe0teBGJocmWhgwccA1GeFXqxzILIxXpHbl9Q/Kw==";
      };
    }
    {
      name = "esbuild_windows_32___esbuild_windows_32_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_windows_32___esbuild_windows_32_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-windows-32/-/esbuild-windows-32-0.14.54.tgz";
        sha512 = "T+rdZW19ql9MjS7pixmZYVObd9G7kcaZo+sETqNH4RCkuuYSuv9AGHUVnPoP9hhuE1WM1ZimHz1CIBHBboLU7w==";
      };
    }
    {
      name = "esbuild_windows_64___esbuild_windows_64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_windows_64___esbuild_windows_64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-windows-64/-/esbuild-windows-64-0.14.54.tgz";
        sha512 = "AoHTRBUuYwXtZhjXZbA1pGfTo8cJo3vZIcWGLiUcTNgHpJJMC1rVA44ZereBHMJtotyN71S8Qw0npiCIkW96cQ==";
      };
    }
    {
      name = "esbuild_windows_arm64___esbuild_windows_arm64_0.14.54.tgz";
      path = fetchurl {
        name = "esbuild_windows_arm64___esbuild_windows_arm64_0.14.54.tgz";
        url  = "https://registry.yarnpkg.com/esbuild-windows-arm64/-/esbuild-windows-arm64-0.14.54.tgz";
        sha512 = "M0kuUvXhot1zOISQGXwWn6YtS+Y/1RT9WrVIOywZnJHo3jCDyewAc79aKNQWFCQm+xNHVTq9h8dZKvygoXQQRg==";
      };
    }
    {
      name = "https___registry.npmjs.org_esbuild___esbuild_0.14.54.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_esbuild___esbuild_0.14.54.tgz";
        url  = "https://registry.npmjs.org/esbuild/-/esbuild-0.14.54.tgz";
        sha512 = "Cy9llcy8DvET5uznocPyqL3BFRrFXSVqbgpMJ9Wz8oVjZlh/zUSNbPRbov0VX7VxN2JH1Oa0uNxZ7eLRb62pJA==";
      };
    }
    {
      name = "https___registry.npmjs.org_escalade___escalade_3.1.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_escalade___escalade_3.1.1.tgz";
        url  = "https://registry.npmjs.org/escalade/-/escalade-3.1.1.tgz";
        sha512 = "k0er2gUkLf8O0zKJiAhmkTnJlTvINGv7ygDNPbeIsX/TJjGJZHuh9B2UxbsaEkmlEo9MfhrSzmhIlhRlI2GXnw==";
      };
    }
    {
      name = "https___registry.npmjs.org_escape_string_regexp___escape_string_regexp_1.0.5.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_escape_string_regexp___escape_string_regexp_1.0.5.tgz";
        url  = "https://registry.npmjs.org/escape-string-regexp/-/escape-string-regexp-1.0.5.tgz";
        sha512 = "vbRorB5FUQWvla16U8R/qgaFIya2qGzwDrNmCZuYKrbdSUMG6I1ZCGQRefkRVhuOkIGVne7BQ35DSfo1qvJqFg==";
      };
    }
    {
      name = "https___registry.npmjs.org_estree_walker___estree_walker_2.0.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_estree_walker___estree_walker_2.0.2.tgz";
        url  = "https://registry.npmjs.org/estree-walker/-/estree-walker-2.0.2.tgz";
        sha512 = "Rfkk/Mp/DL7JVje3u18FxFujQlTNR2q6QfMSMB7AvCBx91NGj/ba3kCfza0f6dVDbw7YlRf/nDrn7pQrCCyQ/w==";
      };
    }
    {
      name = "https___registry.npmjs.org_exenv_es6___exenv_es6_1.1.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_exenv_es6___exenv_es6_1.1.1.tgz";
        url  = "https://registry.npmjs.org/exenv-es6/-/exenv-es6-1.1.1.tgz";
        sha512 = "vlVu3N8d6yEMpMsEm+7sUBAI81aqYYuEvfK0jNqmdb/OPXzzH7QWDDnVjMvDSY47JdHEqx/dfC/q8WkfoTmpGQ==";
      };
    }
    {
      name = "fsevents___fsevents_2.3.2.tgz";
      path = fetchurl {
        name = "fsevents___fsevents_2.3.2.tgz";
        url  = "https://registry.yarnpkg.com/fsevents/-/fsevents-2.3.2.tgz";
        sha512 = "xiqMQR4xAeHTuB9uWm+fFRcIOgKBMiOBP+eXiyT7jsgVCq1bkVygt00oASowB7EdtpOHaaPgKt812P9ab+DDKA==";
      };
    }
    {
      name = "https___registry.npmjs.org_function_bind___function_bind_1.1.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_function_bind___function_bind_1.1.1.tgz";
        url  = "https://registry.npmjs.org/function-bind/-/function-bind-1.1.1.tgz";
        sha512 = "yIovAzMX49sF8Yl58fSCWJ5svSLuaibPxXQJFLmBObTuCr0Mf1KiPopGM9NiFjiYBCbfaa2Fh6breQ6ANVTI0A==";
      };
    }
    {
      name = "https___registry.npmjs.org_gensync___gensync_1.0.0_beta.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_gensync___gensync_1.0.0_beta.2.tgz";
        url  = "https://registry.npmjs.org/gensync/-/gensync-1.0.0-beta.2.tgz";
        sha512 = "3hN7NaskYvMDLQY55gnW3NQ+mesEAepTqlg+VEbj7zzqEMBVNhzcGYYeqFo/TlYz6eQiFcp1HcsCZO+nGgS8zg==";
      };
    }
    {
      name = "https___registry.npmjs.org_globals___globals_11.12.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_globals___globals_11.12.0.tgz";
        url  = "https://registry.npmjs.org/globals/-/globals-11.12.0.tgz";
        sha512 = "WOBp/EEGUiIsJSp7wcv/y6MO+lV9UoncWqxuFfm8eBwzWNgyfBd6Gz+IeKQ9jCmyhoH99g15M3T+QaVHFjizVA==";
      };
    }
    {
      name = "https___registry.npmjs.org_has_flag___has_flag_3.0.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_has_flag___has_flag_3.0.0.tgz";
        url  = "https://registry.npmjs.org/has-flag/-/has-flag-3.0.0.tgz";
        sha512 = "sKJf1+ceQBr4SMkvQnBDNDtf4TXpVhVGateu0t918bl30FnbE2m4vNLX+VWe/dpjlb+HugGYzW7uQXH98HPEYw==";
      };
    }
    {
      name = "https___registry.npmjs.org_has___has_1.0.3.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_has___has_1.0.3.tgz";
        url  = "https://registry.npmjs.org/has/-/has-1.0.3.tgz";
        sha512 = "f2dvO0VU6Oej7RkWJGrehjbzMAjFp5/VKPp5tTpWIV4JHHZK1/BxbFRtf/siA2SWTe09caDmVtYYzWEIbBS4zw==";
      };
    }
    {
      name = "https___registry.npmjs.org_is_core_module___is_core_module_2.11.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_is_core_module___is_core_module_2.11.0.tgz";
        url  = "https://registry.npmjs.org/is-core-module/-/is-core-module-2.11.0.tgz";
        sha512 = "RRjxlvLDkD1YJwDbroBHMb+cukurkDWNyHx7D3oNB5x9rb5ogcksMC5wHCadcXoo67gVr/+3GFySh3134zi6rw==";
      };
    }
    {
      name = "https___registry.npmjs.org_js_tokens___js_tokens_4.0.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_js_tokens___js_tokens_4.0.0.tgz";
        url  = "https://registry.npmjs.org/js-tokens/-/js-tokens-4.0.0.tgz";
        sha512 = "RdJUflcE3cUzKiMqQgsCu06FPu9UdIJO0beYbPhHN4k6apgJtifcoCtT9bcxOpYBtpD2kCM6Sbzg4CausW/PKQ==";
      };
    }
    {
      name = "https___registry.npmjs.org_jsesc___jsesc_2.5.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_jsesc___jsesc_2.5.2.tgz";
        url  = "https://registry.npmjs.org/jsesc/-/jsesc-2.5.2.tgz";
        sha512 = "OYu7XEzjkCQ3C5Ps3QIZsQfNpqoJyZZA99wd9aWd05NCtC5pWOkShK2mkL6HXQR6/Cy2lbNdPlZBpuQHXE63gA==";
      };
    }
    {
      name = "https___registry.npmjs.org_json5___json5_2.2.3.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_json5___json5_2.2.3.tgz";
        url  = "https://registry.npmjs.org/json5/-/json5-2.2.3.tgz";
        sha512 = "XmOWe7eyHYH14cLdVPoyg+GOH3rYX++KpzrylJwSW98t3Nk+U8XOl8FWKOgwtzdb8lXGf6zYwDUzeHMWfxasyg==";
      };
    }
    {
      name = "https___registry.npmjs.org_loose_envify___loose_envify_1.4.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_loose_envify___loose_envify_1.4.0.tgz";
        url  = "https://registry.npmjs.org/loose-envify/-/loose-envify-1.4.0.tgz";
        sha512 = "lyuxPGr/Wfhrlem2CL/UcnUc1zcqKAImBDzukY7Y5F/yQiNdko6+fRLevlw1HgMySw7f611UIY408EtxRSoK3Q==";
      };
    }
    {
      name = "https___registry.npmjs.org_lru_cache___lru_cache_5.1.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_lru_cache___lru_cache_5.1.1.tgz";
        url  = "https://registry.npmjs.org/lru-cache/-/lru-cache-5.1.1.tgz";
        sha512 = "KpNARQA3Iwv+jTA0utUVVbrh+Jlrr1Fv0e56GGzAFOXN7dk/FviaDW8LHmK52DlcH4WP2n6gI8vN1aesBFgo9w==";
      };
    }
    {
      name = "https___registry.npmjs.org_ms___ms_2.1.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_ms___ms_2.1.2.tgz";
        url  = "https://registry.npmjs.org/ms/-/ms-2.1.2.tgz";
        sha512 = "sGkPx+VjMtmA6MX27oA4FBFELFCZZ4S4XqeGOXCv68tT+jb3vk/RyaKWP0PTKyWtmLSM0b+adUTEvbs1PEaH2w==";
      };
    }
    {
      name = "nanoid___nanoid_3.3.8.tgz";
      path = fetchurl {
        name = "nanoid___nanoid_3.3.8.tgz";
        url  = "https://registry.yarnpkg.com/nanoid/-/nanoid-3.3.8.tgz";
        sha512 = "WNLf5Sd8oZxOm+TzppcYk8gVOgP+l58xNy58D0nbUnOxOWRWvlcCV4kUF7ltmI6PsrLl/BgKEyS4mqsGChFN0w==";
      };
    }
    {
      name = "https___registry.npmjs.org_node_releases___node_releases_2.0.8.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_node_releases___node_releases_2.0.8.tgz";
        url  = "https://registry.npmjs.org/node-releases/-/node-releases-2.0.8.tgz";
        sha512 = "dFSmB8fFHEH/s81Xi+Y/15DQY6VHW81nXRj86EMSL3lmuTmK1e+aT4wrFCkTbm+gSwkw4KpX+rT/pMM2c1mF+A==";
      };
    }
    {
      name = "https___registry.npmjs.org_object_assign___object_assign_4.1.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_object_assign___object_assign_4.1.1.tgz";
        url  = "https://registry.npmjs.org/object-assign/-/object-assign-4.1.1.tgz";
        sha512 = "rJgTQnkUnH1sFw8yT6VSU3zD3sWmu6sZhIseY8VX+GRu3P6F7Fu+JNDoXfklElbLJSnc3FUQHVe4cU5hj+BcUg==";
      };
    }
    {
      name = "https___registry.npmjs.org_path_parse___path_parse_1.0.7.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_path_parse___path_parse_1.0.7.tgz";
        url  = "https://registry.npmjs.org/path-parse/-/path-parse-1.0.7.tgz";
        sha512 = "LDJzPVEEEPR+y48z93A0Ed0yXb8pAByGWo/k5YYdYgpY2/2EsOsksJrq7lOHxryrVOn1ejG6oAp8ahvOIQD8sw==";
      };
    }
    {
      name = "https___registry.npmjs.org_picocolors___picocolors_1.0.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_picocolors___picocolors_1.0.0.tgz";
        url  = "https://registry.npmjs.org/picocolors/-/picocolors-1.0.0.tgz";
        sha512 = "1fygroTLlHu66zi26VoTDv8yRgm0Fccecssto+MhsZ0D/DGW2sm8E8AjW7NU5VVTRt5GxbeZ5qBuJr+HyLYkjQ==";
      };
    }
    {
      name = "https___registry.npmjs.org_picomatch___picomatch_2.3.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_picomatch___picomatch_2.3.1.tgz";
        url  = "https://registry.npmjs.org/picomatch/-/picomatch-2.3.1.tgz";
        sha512 = "JU3teHTNjmE2VCGFzuY8EXzCDVwEqB2a8fsIvwaStHhAWJEeVd1o1QD80CU6+ZdEXXSLbSsuLwJjkCBWqRQUVA==";
      };
    }
    {
      name = "postcss___postcss_8.4.31.tgz";
      path = fetchurl {
        name = "postcss___postcss_8.4.31.tgz";
        url  = "https://registry.yarnpkg.com/postcss/-/postcss-8.4.31.tgz";
        sha512 = "PS08Iboia9mts/2ygV3eLpY5ghnUcfLV/EXTOW1E2qYxJKGGBUtNjN76FYHnMs36RmARn41bC0AZmn+rR0OVpQ==";
      };
    }

    {
      name = "https___registry.npmjs.org_react_dom___react_dom_17.0.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_react_dom___react_dom_17.0.2.tgz";
        url  = "https://registry.npmjs.org/react-dom/-/react-dom-17.0.2.tgz";
        sha512 = "s4h96KtLDUQlsENhMn1ar8t2bEa+q/YAtj8pPPdIjPDGBDIVNsrD9aXNWqspUe6AzKCIG0C1HZZLqLV7qpOBGA==";
      };
    }
    {
      name = "react_hook___react_hook_0.0.1.tgz";
      path = fetchurl {
        name = "react_hook___react_hook_0.0.1.tgz";
        url  = "https://registry.yarnpkg.com/react-hook/-/react-hook-0.0.1.tgz";
        sha512 = "2/Guf88/dGyFgUT7QDtBJ1l7V5yqTcAHlNRIZNTu2xg0KkDjaiYZp79ah49NDaLMI/J7voWcKLU8wMONG4A/1g==";
      };
    }
    {
      name = "react_icons___react_icons_4.7.1.tgz";
      path = fetchurl {
        name = "react_icons___react_icons_4.7.1.tgz";
        url  = "https://registry.yarnpkg.com/react-icons/-/react-icons-4.7.1.tgz";
        sha512 = "yHd3oKGMgm7zxo3EA7H2n7vxSoiGmHk5t6Ou4bXsfcgWyhfDKMpyKfhHR6Bjnn63c+YXBLBPUql9H4wPJM6sXw==";
      };
    }
    {
      name = "https___registry.npmjs.org_react_refresh___react_refresh_0.13.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_react_refresh___react_refresh_0.13.0.tgz";
        url  = "https://registry.npmjs.org/react-refresh/-/react-refresh-0.13.0.tgz";
        sha512 = "XP8A9BT0CpRBD+NYLLeIhld/RqG9+gktUjW1FkE+Vm7OCinbG1SshcK5tb9ls4kzvjZr9mOQc7HYgBngEyPAXg==";
      };
    }
    {
      name = "https___registry.npmjs.org_react___react_17.0.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_react___react_17.0.2.tgz";
        url  = "https://registry.npmjs.org/react/-/react-17.0.2.tgz";
        sha512 = "gnhPt75i/dq/z3/6q/0asP78D0u592D5L1pd7M8P+dck6Fu/jJeL6iVVK23fptSUZj8Vjf++7wXA8UNclGQcbA==";
      };
    }
    {
      name = "https___registry.npmjs.org_resolve___resolve_1.22.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_resolve___resolve_1.22.1.tgz";
        url  = "https://registry.npmjs.org/resolve/-/resolve-1.22.1.tgz";
        sha512 = "nBpuuYuY5jFsli/JIs1oldw6fOQCBioohqWZg/2hiaOybXOft4lonv85uDOKXdf8rhyK159cxU5cDcK/NKk8zw==";
      };
    }
    {
      name = "https___registry.npmjs.org_rollup___rollup_2.77.3.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_rollup___rollup_2.77.3.tgz";
        url  = "https://registry.npmjs.org/rollup/-/rollup-2.77.3.tgz";
        sha512 = "/qxNTG7FbmefJWoeeYJFbHehJ2HNWnjkAFRKzWN/45eNBBF/r8lo992CwcJXEzyVxs5FmfId+vTSTQDb+bxA+g==";
      };
    }
    {
      name = "https___registry.npmjs.org_scheduler___scheduler_0.20.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_scheduler___scheduler_0.20.2.tgz";
        url  = "https://registry.npmjs.org/scheduler/-/scheduler-0.20.2.tgz";
        sha512 = "2eWfGgAqqWFGqtdMmcL5zCMK1U8KlXv8SQFGglL3CEtd0aDVDWgeF/YoCmvln55m5zSk3J/20hTaSBeSObsQDQ==";
      };
    }
    {
      name = "semver___semver_6.3.1.tgz";
      path = fetchurl {
        name = "semver___semver_6.3.1.tgz";
        url  = "https://registry.yarnpkg.com/semver/-/semver-6.3.1.tgz";
        sha512 = "BR7VvDCVHO+q2xBEWskxS6DJE1qRnb7DxzUrogb71CWoSficBxYsiAGd+Kl0mmq/MprG9yArRkyrQxTO6XjMzA==";
      };
    }
    {
      name = "https___registry.npmjs.org_source_map_js___source_map_js_1.0.2.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_source_map_js___source_map_js_1.0.2.tgz";
        url  = "https://registry.npmjs.org/source-map-js/-/source-map-js-1.0.2.tgz";
        sha512 = "R0XvVJ9WusLiqTCEiGCmICCMplcCkIwwR11mOSD9CR5u+IXYdiseeEuXCVAjS54zqwkLcPNnmU4OeJ6tUrWhDw==";
      };
    }
    {
      name = "https___registry.npmjs.org_supports_color___supports_color_5.5.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_supports_color___supports_color_5.5.0.tgz";
        url  = "https://registry.npmjs.org/supports-color/-/supports-color-5.5.0.tgz";
        sha512 = "QjVjwdXIt408MIiAqCX4oUKsgU2EqAGzs2Ppkm4aQYbjm+ZEWEcW4SfFNTr4uMNZma0ey4f5lgLrkB0aX0QMow==";
      };
    }
    {
      name = "https___registry.npmjs.org_supports_preserve_symlinks_flag___supports_preserve_symlinks_flag_1.0.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_supports_preserve_symlinks_flag___supports_preserve_symlinks_flag_1.0.0.tgz";
        url  = "https://registry.npmjs.org/supports-preserve-symlinks-flag/-/supports-preserve-symlinks-flag-1.0.0.tgz";
        sha512 = "ot0WnXS9fgdkgIcePe6RHNk1WA8+muPa6cSjeR3V8K27q9BB1rTE3R1p7Hv0z1ZyAc8s6Vvv8DIyWf681MAt0w==";
      };
    }
    {
      name = "https___registry.npmjs.org_tabbable___tabbable_5.3.3.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_tabbable___tabbable_5.3.3.tgz";
        url  = "https://registry.npmjs.org/tabbable/-/tabbable-5.3.3.tgz";
        sha512 = "QD9qKY3StfbZqWOPLp0++pOrAVb/HbUi5xCc8cUo4XjP19808oaMiDzn0leBY5mCespIBM0CIZePzZjgzR83kA==";
      };
    }
    {
      name = "https___registry.npmjs.org_to_fast_properties___to_fast_properties_2.0.0.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_to_fast_properties___to_fast_properties_2.0.0.tgz";
        url  = "https://registry.npmjs.org/to-fast-properties/-/to-fast-properties-2.0.0.tgz";
        sha512 = "/OaKK0xYrs3DmxRYqL/yDc+FxFUVYhDlXMhRmv3z915w2HF1tnN1omB354j8VUGO/hbRzyD6Y3sA7v7GS/ceog==";
      };
    }
    {
      name = "https___registry.npmjs.org_tslib___tslib_1.14.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_tslib___tslib_1.14.1.tgz";
        url  = "https://registry.npmjs.org/tslib/-/tslib-1.14.1.tgz";
        sha512 = "Xni35NKzjgMrwevysHTCArtLDpPvye8zV/0E4EyYn43P7/7qvQwPh9BGkHewbMulVntbigmcT7rdX3BNo9wRJg==";
      };
    }
    {
      name = "https___registry.npmjs.org_typescript___typescript_4.9.4.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_typescript___typescript_4.9.4.tgz";
        url  = "https://registry.npmjs.org/typescript/-/typescript-4.9.4.tgz";
        sha512 = "Uz+dTXYzxXXbsFpM86Wh3dKCxrQqUcVMxwU54orwlJjOpO3ao8L7j5lH+dWfTwgCwIuM9GQ2kvVotzYJMXTBZg==";
      };
    }
    {
      name = "https___registry.npmjs.org_update_browserslist_db___update_browserslist_db_1.0.10.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_update_browserslist_db___update_browserslist_db_1.0.10.tgz";
        url  = "https://registry.npmjs.org/update-browserslist-db/-/update-browserslist-db-1.0.10.tgz";
        sha512 = "OztqDenkfFkbSG+tRxBeAnCVPckDBcvibKd35yDONx6OU8N7sqgwc7rCbkJ/WcYtVRZ4ba68d6byhC21GFh7sQ==";
      };
    }
    {
      name = "uuid___uuid_8.3.2.tgz";
      path = fetchurl {
        name = "uuid___uuid_8.3.2.tgz";
        url  = "https://registry.yarnpkg.com/uuid/-/uuid-8.3.2.tgz";
        sha512 = "+NYs2QeMWy+GWFOEm9xnn6HCDp0l7QBD7ml8zLUmJ+93Q5NF0NocErnwkTkXVFNiX3/fpC6afS8Dhb/gz7R7eg==";
      };
    }
    {
      name = "uuidv4___uuidv4_6.2.13.tgz";
      path = fetchurl {
        name = "uuidv4___uuidv4_6.2.13.tgz";
        url  = "https://registry.yarnpkg.com/uuidv4/-/uuidv4-6.2.13.tgz";
        sha512 = "AXyzMjazYB3ovL3q051VLH06Ixj//Knx7QnUSi1T//Ie3io6CpsPu9nVMOx5MoLWh6xV0B9J0hIaxungxXUbPQ==";
      };
    }
    {
      name = "vite___vite_2.9.18.tgz";
      path = fetchurl {
        name = "vite___vite_2.9.18.tgz";
        url  = "https://registry.yarnpkg.com/vite/-/vite-2.9.18.tgz";
        sha512 = "sAOqI5wNM9QvSEE70W3UGMdT8cyEn0+PmJMTFvTB8wB0YbYUWw3gUbY62AOyrXosGieF2htmeLATvNxpv/zNyQ==";
      };
    }
    {
      name = "https___registry.npmjs.org_yallist___yallist_3.1.1.tgz";
      path = fetchurl {
        name = "https___registry.npmjs.org_yallist___yallist_3.1.1.tgz";
        url  = "https://registry.npmjs.org/yallist/-/yallist-3.1.1.tgz";
        sha512 = "a4UGQaWPH59mOXUYnAG2ewncQS4i4F43Tv3JoAM+s2VDAmS9NsK8GpDMLrCHPksFT7h3K6TOoUNn2pb7RoXx4g==";
      };
    }
  ];
}
