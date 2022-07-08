# Getting Started Guide

This is the Coq proof artifacts of the paper /A case for DOT: Theoretical Foundations for Objects With Pattern Matching and GADT-style Reasoning/. It consists of the following parts:

- The `cdot/` directory contains sources of the mechanization of the cDOT calculus.
  The proof is an extension of [pDOT soundness proof](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths).
- The `lambda2GMu/` directory contains sources of the mechanization of the Lambda2Gmu calculus and `lambda2GMu_annotated/` contains sources of the variant with additional type annotations, as described in the paper.
- The `translation/` directory contains lemmas related to the translation: the typing of the `lib` term and an example showing inversion of tuple equality using our added inversion rules.

## Prerequisites

To compile the proof, the following softwares and libraries are needed.

- Coq 8.13.0
- TLC library

There are two ways to setup these requirements, even with OPAM or using a Docker container.

### Setting up with OPAM

The easiest way is to use OPAM.

```
opam repo add coq-released http://coq.inria.fr/opam/released
opam pin add coq 8.13.0
opam install -j4 coq-tlc
```

### Using a Docker container

TODO

## Compiling the Proof

We provide a Makefile for each part of our proof. To compile them, `cd` to the corresponding directory and execute `make`. For example, to compile the mechanization of cDOT calculus, assuming that you are at the root directory of our artifact:
```
cd cdot/
make
```

The translation proofs rely on cdot, so the cdot directory should be built first before attempting to build translation. Similarly, lambda2GMu_annotated depends on lambda2GMu so it also should be compiled in the proper order.

If `make` exits without error, the proof is compiled successfully.

