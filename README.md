# KEMEDHOC*
A formally verified implementation of KEMEDHOC, a quantum-safe variant of EDHOC, using
F*/Low*/KaRaMel toolchain.

# Dependencies
## Ocaml
```sh
# install Ocaml
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
opam init
eval $(opam env)
```

## Z3 SMT solver
As `FStar` only works on specific Z3 versions, 4.8.5 and 4.13.3, so you need install
either particular version of Z3. Run the script provided at [get_fstar_z3.sh](https://github.com/FStarLang/FStar/blob/master/.scripts/get_fstar_z3.sh)
to get required Z3 packages.

## FStar
```sh
# install the latest version of FStar
opam pin add fstar --dev-repo
```

## KaRaMel
```sh
# install the latest version of KaRaMel compiler
opam pin add karamel --dev-repo
```

Once required packages are installed, please remember to run `eval $(opam eval)`
to activate the environment containing installed packages.