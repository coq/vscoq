{ pkgs ? (import <nixpkgs> {})
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages
}:

with pkgs;

stdenv.mkDerivation rec {

  name = "vscoq";
  src = null;

  buildInputs = [
    wget
    nodejs
    nodePackages.npm
    ocamlPackages.ocaml
    ocamlPackages.dune_2
    ocamlPackages.yojson
    ocamlPackages.findlib
    ocamlPackages.zarith
    ocamlPackages.ocaml-lsp
  ];

}
