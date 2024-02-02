{
  description = "VsCoq 2, a language server for Coq based on LSP";

  inputs = {

    flake-utils.url = "github:numtide/flake-utils";

  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
  
   rec {

    packages.default = self.packages.${system}.vscoq-language-server;

    packages.vscoq-language-server =
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

    devShells.vscoq-language-server = 
      with import nixpkgs { inherit system; };
      mkShell {
        buildInputs =
          self.packages.${system}.vscoq-language-server.buildInputs;
      };

    devShells.default = 
      with import nixpkgs { inherit system; };
      mkShell {
        buildInputs =
          self.packages.${system}.vscoq-language-server.buildInputs
          ++ (with ocamlPackages; [
            ocaml-lsp
          ]);
      };

  });
}
