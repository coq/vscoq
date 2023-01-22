{ pkgs ? (import <nixpkgs> {})
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages_4_14
}:

with pkgs;

stdenv.mkDerivation rec {

  name = "vscoq";
  src = null;

  buildInputs = [
    hostname
    python3
    time
    nodejs
    yarn
    nodePackages.yo
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
  ]);

}
