{
  description = "VsCoq 2, a language server for Coq based on LSP";

  outputs = { self, nixpkgs }: {

    defaultPackage.x86_64-linux =
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
          ocaml-lsp
          ppx_inline_test
          ppx_assert
          ppx_sexp_conv
          sexplib
          ppx_yojson_conv
        ]);
      };

  };
}
