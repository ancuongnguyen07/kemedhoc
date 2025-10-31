#! /bin/bash
set -e

opam_install() {
    # unsafe-yes for auto-installing external dependencies
    opam install -y --confirm-level=unsafe-yes "$1"
}

# install Ocaml
# bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
apt install -y opam
opam -y init
opam switch create 4.12.0
eval $(opam env --switch=4.12.0)

# install ProVerif
opam_install proverif

# install Z3 Solver
./scripts/get_fstar_z3.sh /usr/local/bin

# install F*
opam_install fstar

# install KaRaMel
opam_install karamel