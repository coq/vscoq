#!/bin/bash

repo=$PWD/_build/opam-repository
rm -rf $repo

function mkp {
  local P="$1"
  local V="$2"
  local D="$3"

  mkdir -p $repo/packages/$P/$P.$V/
  (cd $D; git archive --format=tar.gz --prefix=$P-$V/ -o $repo/$P.tar.gz HEAD)
  cp $D/$P.opam $repo/packages/$P/$P.$V/opam
  echo -e "\nurl {\n src: \"file://$repo/$P.tar.gz\"\n checksum: \"sha256=$(sha256sum $repo/$P.tar.gz|cut -f 1 -d ' ')\"\n }" >> $repo/packages/$P/$P.$V/opam
  sed -i '/version: "dev"/d' $repo/packages/$P/$P.$V/opam
}

mkp vscoq-language-server 0.1          ./

cd $repo
opam admin lint
