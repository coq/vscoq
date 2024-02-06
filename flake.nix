{
  description = "VsCoq 2, a language server for Coq based on LSP";

  inputs = {

    flake-utils.url = "github:numtide/flake-utils";

    coq-master = { url = "github:coq/coq/b157d65080076498ad04dd3918c1e508eb9740c0"; }; # Should be kept in sync with PIN_COQ in CI workflow
    coq-master.inputs.nixpkgs.follows = "nixpkgs";

  };

  outputs = { self, nixpkgs, flake-utils, coq-master }:
    flake-utils.lib.eachDefaultSystem (system:
  
   let coq = coq-master.defaultPackage.${system}; in
   rec {

    packages.default = self.packages.${system}.vscoq-language-server-coq-8-19;

    packages.vscoq-language-server-coq-8-18 =
      # Notice the reference to nixpkgs here.
      with import nixpkgs { inherit system; };
      let ocamlPackages = ocaml-ng.ocamlPackages_4_14; in
      ocamlPackages.buildDunePackage {
        duneVersion = "3";
        pname = "vscoq-language-server";
        version = "2.0.3";
        src = ./language-server;
        buildInputs = [
          coq_8_18
          dune_3
        ] ++ (with coq.ocamlPackages; [
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

      packages.vscoq-language-server-coq-8-19 =
      # Notice the reference to nixpkgs here.
      with import nixpkgs { inherit system; };
      let ocamlPackages = ocaml-ng.ocamlPackages_4_14; in
      ocamlPackages.buildDunePackage {
        duneVersion = "3";
        pname = "vscoq-language-server";
        version = "2.0.3";
        src = ./language-server;
        buildInputs = [
          coq_8_19
          dune_3
        ] ++ (with coq.ocamlPackages; [
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

    packages.vscoq-language-server-coq-master =
      # Notice the reference to nixpkgs here.
      with import nixpkgs { inherit system; };
      let ocamlPackages = ocaml-ng.ocamlPackages_4_14; in
      ocamlPackages.buildDunePackage {
        duneVersion = "3";
        pname = "vscoq-language-server";
        version = "2.0.3";
        src = ./language-server;
        buildInputs = [
          coq
          dune_3
        ] ++ (with coq.ocamlPackages; [
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

    packages.vscoq-client =
      with import nixpkgs { inherit system; };
      stdenv.mkDerivation rec {

        name = "vscoq-client";
        src = ./client;

        buildInputs = [
          nodejs
          yarn
        ];

    };

    devShells.vscoq-client = 
      with import nixpkgs { inherit system; };
      mkShell {
        buildInputs = self.packages.${system}.vscoq-client.buildInputs;
      };

    devShells.vscoq-language-server-coq-8-18 = 
        with import nixpkgs { inherit system; };
        mkShell {
            buildInputs =
            self.packages.${system}.vscoq-language-server-coq-8-18.buildInputs;
        };
        
    devShells.vscoq-language-server-coq-8-19 = 
      with import nixpkgs { inherit system; };
      mkShell {
        buildInputs =
          self.packages.${system}.vscoq-language-server-coq-8-19.buildInputs;
      };
    
    devShells.vscoq-language-server-coq-master = 
      with import nixpkgs { inherit system; };
      let ocamlPackages = ocaml-ng.ocamlPackages_4_14; in
      mkShell {
        buildInputs =
          self.packages.${system}.vscoq-language-server-coq-master.buildInputs
          ++ (with ocamlPackages; [
            ocaml-lsp
          ]);
      };

    devShells.default = 
      with import nixpkgs { inherit system; };
      mkShell {
        buildInputs =
          self.packages.${system}.vscoq-language-server-coq-8-19.buildInputs
          ++ (with ocamlPackages; [
            ocaml-lsp
          ]);
      };

  });
}
