# Getting Started Guide

This is the Coq proof artifacts of the paper *A case for DOT: Theoretical Foundations for Objects With Pattern Matching and GADT-style Reasoning*. It consists of the following parts:

- The `cdot/` directory contains sources of the mechanization of the cDOT calculus.
  The proof is an extension of [pDOT soundness proof](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths).
- The `lambda2GMu/` directory contains sources of the mechanization of the Lambda2Gmu calculus and `lambda2GMu_annotated/` contains sources of the variant with additional type annotations, as described in the paper.
- The `translation/` directory contains lemmas related to the translation: the typing of the `lib` term and an example showing inversion of tuple equality using our added inversion rules.

## Prerequisites

To compile the proof, the following softwares and libraries are needed.

- Coq 8.13.0

- TLC library

There are two ways to setup these requirements, using either OPAM or Docker.

### Setting up with OPAM

This requires you to install OPAM first. After properly setting up OPAM, run the following commands to install the prerequisites:
```
opam repo add coq-released http://coq.inria.fr/opam/released
opam pin add coq 8.13.0
opam install -j4 coq-tlc
```

### Using a Docker container

We have built a Docker image containing all necessary prerequisites and pushed it to [Docker Hub](https://hub.docker.com/r/linyxus/cdot-artifact-env).

To use this image, you should first install Docker if it is not installed yet. Then, you can launch a container using this image with the following command:
```
docker run -it --rm linyxus/cdot-artifact-env
```
You will be attached to the shell of the container after the image gets pulled and the container is launched. In the shell, you will be in a Git repository of our proof artifact, with all prerequisites in the environment. You can now compile the proof artifacts following the instructions in the next section.

The docker image is built on the Coq docker [image](https://hub.docker.com/r/coqorg/coq/). We use [this Dockerfile](https://github.com/Linyxus/cdot-calculus/blob/paper/Dockerfile) to build the image. Compared to the publicly available Coq image, our image have the TLC library pre-installed and have the Git respository of our proof artifacts.

## Compiling the Proof

We provide a Makefile for each part of our proof. The translation proofs rely on `cdot` and `lambda2GMu_annotated`, and `lambda2GMu_annotated` itself relies on `lambda2GMu`. So the proof artifacts have to be compiled in the proper order.

To compile each of them, `cd` to the corresponding directory and execute `make`. For example, to compile the mechanization of cDOT calculus, assuming that you are at the root directory of our artifact:
```
cd cdot/
make
```

If `make` exits without error, the proof is compiled successfully.

