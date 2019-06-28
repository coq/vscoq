{ pkgs ? (import <nixpkgs> {})
, ocamlPackages ? pkgs.ocaml-ng.ocamlPackages_4_06
}:

with pkgs;

stdenv.mkDerivation rec {

  name = "vscoq";
  src = null;

  buildInputs = [
    wget
    nodejs
    nodePackages.npm
  ];

}
