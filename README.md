# Soundness Proof for Extended pDOT Calculus

This repository contains type safety proof for the extended pDOT system,
mechanized in Coq.

The calculus is extended with the following record subtyping inversion rules,
which will facilitate the formalization of GADT reasoning in pDOT.

```
G ⊢ U1 <: U2
U1 ↘ {A: S1..T1}
U2 ↘ {A: S2..T2}
_________________
G ⊢ S2 <: S1

G ⊢ U1 <: U2
U1 ↘ {A: S1..T1}
U2 ↘ {A: S2..T2}
_________________
G ⊢ T1 <: T2
```

The proof is modified from [pDOT soundness
proof](https://github.com/amaurremi/dot-calculus/tree/master/src/extensions/paths).

