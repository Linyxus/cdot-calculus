

# Structure

- The `cdot/` directory contains sources of the mechanization of the iDOT calculus.
  The proof is an extension of [pDOT soundness proof](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths).
- The `lambda2GMu/` directory contains sources of the mechanization of the Lambda2Gmu calculus and `lambda2GMu_annotated/` contains sources of the variant with additional type annotations, as described in the paper.
- The `translation/` directory contains lemmas related to the translation: the typing of the `lib` term and an example showing inversion of tuple equality using our added inversion rules.

## Building the proofs

The proofs require Coq 8.13.0 and the TLC library. The easiest way to obtain them is to use OPAM:

```
opam repo add coq-released http://coq.inria.fr/opam/released
opam pin add coq 8.13.0
opam install -j4 coq-tlc
```

Then, in each directory the proofs can be built using the `make` command.

The `translation` proofs rely on `cdot`, so the `cdot` directory should be built first before attempting to build `translation`.
Similarly, `lambda2GMu_annotated` depends on `lambda2GMu` so it also should be compiled in the proper order.

The builds were tested on a Linux machine, running Ubuntu 18.04.6 LTS and on macOS (12.3.1), but it should be possible to reproduce them on other systems as well - the details of retrieving the specific version of Coq may vary slightly.
