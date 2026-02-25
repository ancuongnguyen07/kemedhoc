# KEMEDHOC*
An implementation of KEMEDHOC, including machine-checked proofs, a quantum-safe variant of EDHOC key exchange protocol ([RFC9528](https://datatracker.ietf.org/doc/html/rfc9528)),
powered by F*/Low*/KaRaMel toolchain.

The protocol design and implementation detail are available in [my thesis](./docs/master_thesis_2025.pdf).

This is a _research artifact_, not a production-ready software. Please
use the library with your _own risk_.

Table of contents:
- [KEMEDHOC\*](#kemedhoc)
- [Installing Dependencies](#installing-dependencies)
  - [Ocaml](#ocaml)
  - [ProVerif](#proverif)
  - [Z3 SMT solver](#z3-smt-solver)
  - [FStar](#fstar)
  - [KaRaMel](#karamel)
  - [Dockerfile](#dockerfile)
- [Verifying protocol](#verifying-protocol)
  - [EDHOC\*](#edhoc)
  - [KEMEDHOC\*](#kemedhoc-1)
  - [KEMEDHOC ProVerif model](#kemedhoc-proverif-model)
- [Running protocol](#running-protocol)


# Installing Dependencies

## Ocaml
```sh
# install Ocaml
bash -c "sh <(curl -fsSL https://opam.ocaml.org/install.sh)"
opam init
opam switch create 4.12.0
eval $(opam env --switch=4.12.0)
```

## ProVerif
```sh
# install graphviz if you do not already have
# graphviz is required for visualizing function of ProVerif,
# e.g., illustration of attack traces.
opam depext proverif
opam install proverif
```

## Z3 SMT solver
As `FStar` only works on specific Z3 versions, 4.8.5 and 4.13.3, so you need install
either particular version of Z3. Run the script provided at [get_fstar_z3.sh](https://github.com/FStarLang/FStar/blob/master/.scripts/get_fstar_z3.sh)
to get required Z3 packages.
```sh
./scripts/get_fstar_z3.sh /usr/local/bin
```

Check if you have installed them correctly
```sh
z3-4.13.3 --version
> Z3 version 4.13.3
z3-4.8.5 --version
> Z3 version 4.8.5
```

## FStar
```sh
opam install fstar
```

## KaRaMel
```sh
# install the latest version of KaRaMel compiler
opam install karamel
```

Once required packages are installed, please remember to run `eval $(opam eval --switch=default)`
to activate the environment containing installed packages.

## Dockerfile
Instead of manually installing dependencies, which is occasionally annoying, you
can build and run the pre-defined Docker image.
```sh
docker_run.sh
```

# Verifying protocol
## EDHOC*
To verify EDHOC*, run the following command:
```sh
make -C src/edhoc verify
```

## KEMEDHOC*
To verify KEMEDHOC*, run the following command:
```sh
make -C src/kemedhoc verify
```

## KEMEDHOC ProVerif model
To verify KEMEDHOC specification with ProVerif, run the following command
```sh
cd pv-models
./run-proverif.sh -f kemedhoc.pv -D <DEF>
# <DEF> should be [Anonymity, Model, ReflectionSimul]
# - Anonymity: model for validating identity leakage
# - Model: standard model for validating security properties
# - ReflectionSimul: model for validating Reflection/Selfie attack
```

# Running protocol
The experiment setup is based on [uoscore-uedhoc](https://github.com/eriptic/uoscore-uedhoc).

First, open a terminal for Responder and run the following command:
```sh
cd pq-uoscore-uedhoc/samples/linux_edhoc/responder
make
./build/responder
```

Then open another terminal for Initiator and run the following command:
```sh
cd pq-uoscore-uedhoc/samples/linux_edhoc/initiator
make
./build/initiator -q -m <authentication_method>
# -q for employing post-quantum algorithms
# <authentication_method> should be 0-4. Method 4 is for KEMEDHOC
```

You should see the two parties establish a shared session key.
