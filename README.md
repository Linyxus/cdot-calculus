# cDOT soundness proof

This repository contains the mechanised proof of soundness for the OOPSLA 2022 paper "A case for DOT: Theoretical Foundations for Objects With Pattern Matching and GADT-style Reasoning". 

# Inspecting the proof

The initial "kick the tires" guide for getting started with the mechanisation can be found [here](getting-started.md) and as a PDF [here](getting-started.pdf).

The detailed "step by step" guide explaining how to inspect the mechanised proof can be found [here](step-by-step.md) and as a PDF [here](step-by-step.pdf).

# Structure

- The `cdot/` directory contains sources of the mechanization of the iDOT calculus.
  The proof is an extension of [pDOT soundness proof](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths).
- The `lambda2GMu/` directory contains sources of the mechanization of the Lambda2Gmu calculus and `lambda2GMu_annotated/` contains sources of the variant with additional type annotations, as described in the paper.
- The `translation/` directory contains lemmas related to the translation: the typing of the `lib` term and an example showing inversion of tuple equality using our added inversion rules.


