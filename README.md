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

# CTML Core connection and FCCT comparison

The ongoing core-DOT translation targets CTML Core with native records,
intersections, unions, Z, and scoped recursive type declarations. Existential
witnesses are continuation-encoded; records use CTML's own syntax and typing rules.
The bridge is available through `import CDotFCCT.CTML` in the Lean project.
The full typing-preserving translation is unfinished; see the
[translation status](notes/fcct-translation.md) for checked coverage.

The call-by-value FCCT mechanization is available at
[`external/ctml/fcct/lean`](external/ctml/fcct/lean), within a pinned CTML Git
submodule. See the [paper/mechanization review](notes/fcct-review.md) for the
differences from the original FCCT paper, checked proof coverage, and the proposed
connection with cDOT using CPS and a primitive Z combinator.

The submodule now includes the Z primitive, with extended progress, preservation,
and soundness proofs, plus checked terminating and nonterminating examples.

```sh
git submodule update --init external/ctml
cd external/ctml/fcct/lean
lake build
lake env lean ../../../../notes/fcct/Audit.lean
```

Both FCCT and the cDOT Lean port use Lean 4.34.0. FCCT has no Mathlib dependency;
cDOT and CTML Core use the same Mathlib 4.34.0 build cache. Both CTML Core and FCCT
are local Lake dependencies. See the [Lean build guide](lean/README.md) for building
the bridge and both calculi using the cache.
