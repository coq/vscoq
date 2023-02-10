{
  description = "VsCoq 2, a language server for Coq based on LSP";

  outputs = { self, nixpkgs }: {

    packages.x86_64-linux.default = self.packages.x86_64-linux.vscoq-language-server;

    packages.x86_64-linux.vscoq-language-server =
      # Notice the reference to nixpkgs here.
      with import nixpkgs { system = "x86_64-linux"; };
      ocamlPackages.buildDunePackage {
        duneVersion = "3";
        pname = "vscoq-language-server";
        version = "2.0.0-beta1";
        src = ./language-server;
        buildInputs = [
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
          sexplib
          ppx_yojson_conv
        ]);
      };

    packages.x86_64-linux.vscoq-client =
      with import nixpkgs { system = "x86_64-linux"; };
      stdenv.mkDerivation rec {

        name = "vscoq-client";
        src = ./client;

        buildInputs = [
          nodejs
          yarn
        ];

    };

    devShells.x86_64-linux.default =
      with import nixpkgs { system = "x86_64-linux"; };
      mkShell {
        buildInputs =
          self.packages.x86_64-linux.vscoq-language-server.buildInputs
          ++ (with ocamlPackages; [
            ocaml-lsp
          ]);
      };

  };
}
