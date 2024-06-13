{
  description = "VsCoq 2, a language server for Coq based on LSP";

  inputs = {
    flake-utils.url = "github:numtide/flake-utils";

    coq-master = { url = "github:coq/coq/f37ff9690f297074d0c9bd78e6c2c858d2db2e98"; }; # Should be kept in sync with PIN_COQ in CI workflow
    coq-master.inputs.nixpkgs.follows = "nixpkgs";

  };

  outputs = {
    self,
    nixpkgs,
    flake-utils,
    coq-master,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      name = "vscoq-client";
      vscodeExtPublisher = "maximedenes";
      vscodeExtName = "vscoq";
      vscodeExtUniqueId = "maximedenes.vscoq";
      vscoq_version = "2.1.3";
      coq = coq-master.packages.${system};
    in rec {
      formatter = nixpkgs.legacyPackages.${system}.alejandra;

      packages = {
        default = self.packages.${system}.vscoq-language-server-coq-8-19;

        vscoq-language-server-coq-8-18 =
          # Notice the reference to nixpkgs here.
          with import nixpkgs {inherit system;}; let
            ocamlPackages = ocaml-ng.ocamlPackages_4_14;
          in
            ocamlPackages.buildDunePackage {
              duneVersion = "3";
              pname = "vscoq-language-server";
              version = vscoq_version;
              src = ./language-server;
              nativeBuildInputs = [
                coq_8_18
              ];
              buildInputs =
                [
                  coq_8_18
                  dune_3
                ]
                ++ (with coq.ocamlPackages; [
                  lablgtk3-sourceview3
                  glib
                  gnome.adwaita-icon-theme
                  wrapGAppsHook
                  ocaml
                  yojson
                  zarith
                  findlib
                  ppx_inline_test
                  ppx_assert
                  ppx_sexp_conv
                  ppx_deriving
                  ppx_optcomp
                  ppx_import
                  sexplib
                  ppx_yojson_conv
                  lsp
                  sel
                ]);
            };

        vscoq-language-server-coq-8-19 =
          # Notice the reference to nixpkgs here.
          with import nixpkgs {inherit system;}; let
            ocamlPackages = ocaml-ng.ocamlPackages_4_14;
          in
            ocamlPackages.buildDunePackage {
              duneVersion = "3";
              pname = "vscoq-language-server";
              version = vscoq_version;
              src = ./language-server;
              nativeBuildInputs = [
                coq_8_19
              ];
              buildInputs =
                [
                  coq_8_19
                  dune_3
                ]
                ++ (with coq.ocamlPackages; [
                  lablgtk3-sourceview3
                  glib
                  gnome.adwaita-icon-theme
                  wrapGAppsHook
                  ocaml
                  yojson
                  zarith
                  findlib
                  ppx_inline_test
                  ppx_assert
                  ppx_sexp_conv
                  ppx_deriving
                  ppx_optcomp
                  ppx_import
                  sexplib
                  ppx_yojson_conv
                  lsp
                  sel
                ]);
            };

        vscoq-language-server-coq-master =
          # Notice the reference to nixpkgs here.
          with import nixpkgs {inherit system;}; let
            ocamlPackages = ocaml-ng.ocamlPackages_4_14;
          in
            ocamlPackages.buildDunePackage {
              duneVersion = "3";
              pname = "vscoq-language-server";
              version = vscoq_version;
              src = ./language-server;
              nativeBuildInputs = [
                coq
              ];
              buildInputs =
                [
                  coq
                  dune_3
                ]
                ++ (with coq.ocamlPackages; [
                  lablgtk3-sourceview3
                  glib
                  gnome.adwaita-icon-theme
                  wrapGAppsHook
                  ocaml
                  yojson
                  zarith
                  findlib
                  ppx_inline_test
                  ppx_assert
                  ppx_sexp_conv
                  ppx_deriving
                  ppx_optcomp
                  ppx_import
                  sexplib
                  ppx_yojson_conv
                  lsp
                  sel
                ]);
            };

        vscoq-client = with import nixpkgs {inherit system;}; let
          yarn_deps = name: (path: (mkYarnModules {
            pname = "${name}_yarn_deps";
            version = vscoq_version;
            packageJSON = ./${path}/package.json;
            yarnLock = ./${path}/yarn.lock;
            yarnNix = ./${path}/yarn.nix;
          }));

          client_deps = yarn_deps "client" /client;
          goal_view_ui_deps = yarn_deps "goal_ui" /client/goal-view-ui;
          search_ui_deps = yarn_deps "search_ui" /client/search-ui;

          link_deps = x: (p: ''
            ln -s ${x}/node_modules ${p}
            export PATH=${x}/node_modules/.bin:$PATH
          '');

          links = [
            (link_deps client_deps ".")
            (link_deps goal_view_ui_deps "./goal-view-ui")
            (link_deps search_ui_deps "./search-ui")
          ];

          cmds = builtins.concatStringsSep "\n" links;

          src = ./client;

          nativeBuildInputs =
            [
              nodejs
              yarn
            ]
            ++ [client_deps goal_view_ui_deps search_ui_deps];

          installPrefix = "share/vscode/extensions/${vscodeExtUniqueId}";
        in {
          extension = pkgs.vscode-utils.buildVscodeExtension {
            inherit name vscodeExtName vscodeExtPublisher vscodeExtUniqueId src nativeBuildInputs;
            version = vscoq_version;

            buildPhase =
              cmds
              + ''
                cd goal-view-ui
                yarn run build
                cd ../search-ui
                yarn run build
                cd ..
                webpack --mode=production --devtool hidden-source-map
              '';
          };
          vsix_archive = stdenv.mkDerivation {
            name = "vscoq-client-vsix";

            unpackPhase = ''
              cp -r ${self.packages.${system}.vscoq-client.extension}/share/vscode/extensions/${vscodeExtUniqueId}/* .
              ls -alt
              pwd
            '';

            nativeBuildInputs = [
              self.packages.${system}.vscoq-client.extension
              client_deps
              nodejs
              yarn
            ];

            buildPhase = ''
              export PATH=${client_deps}/node_modules/.bin:$PATH
              bash -c "yes y | vsce package"
              mkdir -p $out/share/vscode/extensions
              cp *.vsix $out/share/vscode/extensions
            '';
          };
        };
      };

      devShells = {
        vscoq-client = with import nixpkgs {inherit system;};
          mkShell {
            buildInputs = self.packages.${system}.vscoq-client.extension.buildInputs;
          };

        vscoq-language-server-coq-8-18 = with import nixpkgs {inherit system;}; let
          ocamlPackages = ocaml-ng.ocamlPackages_4_14;
        in
          mkShell {
            buildInputs =
              self.packages.${system}.vscoq-language-server-coq-8-18.buildInputs
              ++ (with ocamlPackages; [
                ocaml-lsp
              ]);
          };

        vscoq-language-server-coq-8-19 = with import nixpkgs {inherit system;}; let
          ocamlPackages = ocaml-ng.ocamlPackages_4_14;
        in
          mkShell {
            buildInputs =
              self.packages.${system}.vscoq-language-server-coq-8-19.buildInputs
              ++ (with ocamlPackages; [
                ocaml-lsp
              ]);
          };

        vscoq-language-server-coq-master = with import nixpkgs {inherit system;}; let
          ocamlPackages = ocaml-ng.ocamlPackages_4_14;
        in
          mkShell {
            buildInputs =
              self.packages.${system}.vscoq-language-server-coq-master.buildInputs
              ++ (with ocamlPackages; [
                ocaml-lsp
              ]);
          };

        default = with import nixpkgs {inherit system;}; let
          ocamlPackages = ocaml-ng.ocamlPackages_4_14;
        in
          mkShell {
            buildInputs =
              self.packages.${system}.vscoq-language-server-coq-8-19.buildInputs
              ++ (with ocamlPackages; [
                ocaml-lsp
              ]);
          };
      };
    });
}
