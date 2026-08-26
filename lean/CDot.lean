import CDot.Definitions
import CDot.Sequences
import CDot.Binding
import CDot.Lookup
import CDot.Reduction
import CDot.Replacement
import CDot.RecordAndInertTypes
import CDot.Weakening
import CDot.Subenvironments
import CDot.Narrowing
import CDot.PreciseFlow
import CDot.PreciseTyping
import CDot.TightTyping
import CDot.InvertibleTyping
import CDot.ReplacementTyping
import CDot.InvertibleSubtyping
import CDot.Substitution
import CDot.GADTRules

/-!
# cDOT in Lean 4

This is the entry point for the Lean port of the cDOT mechanization in
`../cdot`. The modules intentionally follow the dependency structure of the
original Coq development.
-/
