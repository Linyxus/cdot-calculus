import CDotFCCT.CTML.PackageWitnesses
import CTMLCore.Declarative.IndexedSystems

/-!
# Constructing mutually recursive package witnesses

Every interface may refer to every member of the same finite group. The outer
package arrows guard all those references. The system constructs both native
subtyping equations for every name in one context, and its indexed solution
validates them simultaneously.

`Recursive.HasType.recursiveSystem` closes this entire scope after the term and
its result have hidden the names. The rule is covered by the target safety theorem.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.Coercion

open CTMLCore

def recursivePackages {depth size : Nat} (interfaces : Fin size → Interface (depth + size))
    (answer : WFTy depth) : RecursiveSystem depth size :=
  ⟨fun index => (interfaces index).consumer (answer.weakenBy size),
    fun _ => answer.weakenBy size⟩

def PackageWitness.mutual (s : SubtypingContext) {size : Nat}
    (interfaces : Fin size → Interface (s.typeDepth + size)) (answer : WFTy s.typeDepth)
    (index : Fin size) :
    PackageWitness ((recursivePackages interfaces answer).openContext s)
      (answer.weakenBy size) ((recursivePackages interfaces answer).name index) :=
  ⟨(interfaces index).consumer (answer.weakenBy size),
    (recursivePackages interfaces answer).unfold s index,
    (recursivePackages interfaces answer).fold s index⟩

theorem recursivePackages_valid {size : Nat} {s : SubtypingContext}
    {env : Indexed.Environment} {n : Nat} (valid : s.IndexedValidates env n)
    (interfaces : Fin size → Interface (s.typeDepth + size)) (answer : WFTy s.typeDepth) :
    ((recursivePackages interfaces answer).openContext s).IndexedValidates
      ((recursivePackages interfaces answer).indexedEnvironment env) n :=
  (recursivePackages interfaces answer).indexedValidates valid

end CDotFCCT.CTML.Coercion
