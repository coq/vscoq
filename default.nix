{ pkgs ? (import <nixpkgs> {})
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages
}:

with pkgs;

stdenv.mkDerivation rec {

  name = "vscoq";
  src = null;

  buildInputs = [
    nodejs
    yarn
    nodePackages.yo
  ];

}
