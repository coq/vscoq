# For beginners

It is recommended to use the [coq-platform](https://github.com/coq/platform?tab=readme-ov-file#installation).

# For developpers

## Opam

[opam](https://opam.ocaml.org/) is the main OCaml package manager. It is the easyiest way to install Coq and Coq packages.

### Installing opam
The quickest way to install opam is to run this script.
```
bash -c "sh <(curl -fsSL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)"
```
Or for Windows users:
```
Invoke-Expression "& { $(Invoke-RestMethod https://raw.githubusercontent.com/ocaml/opam/master/shell/install.ps1) }"
```
Detailed install instructions can be found [here](https://opam.ocaml.org/doc/Install.html).

### opam switch
Central to using opam is the concept of "switch". A switch is an independant installation prefix with its own set of compiler and **pinned** packages.
With this, a user can seamlesly switch from an environment with different Coq versions and packages installed.
To create a new opam switch simply type:
```
opam switch create name
```
Where ```name``` will be used to reference the switch from here on out.

## Coq

### Installing Coq
After creating a switch, it is simply a matter of typing the following command:
```
opam install coq
```
If you want a specific version of Coq, for example ```8.18.0```, then type:
```
opam pin add coq 8.18.0
```

### Installing vscoq-language-server

To use this extension, it is absolutely necessary to install the vscoq langauge server by typing:
```
opam install vscoq-language-server
```
