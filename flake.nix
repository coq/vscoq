{
  description = "VsCoq 2, a language server for Coq based on LSP";

  inputs = {

    flake-utils.url = "github:numtide/flake-utils";

    coq-8_18 = {
      type = "github";
      owner = "coq";
      repo = "coq";
      ref = "V8.18.0";
    };

    coq-8_18.inputs.nixpkgs.follows = "nixpkgs";

  };

  outputs = { self, nixpkgs, flake-utils, coq-8_18 }:
    flake-utils.lib.eachDefaultSystem (system:
  
   let coq = coq-8_18.defaultPackage.${system}; in
   rec {

    packages.default = self.packages.${system}.vscoq-language-server;

    packages.vscoq-language-server =
      # Notice the reference to nixpkgs here.
      with import nixpkgs { inherit system; };
      
      ocamlPackages.buildDunePackage {
        duneVersion = "3";
        pname = "vscoq-language-server";
        version = "2.0.2";
        src = ./language-server;
        buildInputs = [
          coq
          bash
          hostname
          python3
          time
          dune_3
        ] ++ (with ocamlPackages; [
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
