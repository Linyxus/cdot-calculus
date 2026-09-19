import CDot.Definitions

/-!
# The complete core-DOT input judgment

These data-valued derivations use the repository's actual syntax, contexts, and
binding conventions. They include functions, recursive and nested objects, bounds,
intersections, recursive opening/closing, and singleton/path transport. The cDOT
tag-test rule and inversion rules are omitted. Object tags remain in the source
syntax and retain their source typing premise, even though the target erases them.

Keeping derivations in `Type` lets a compiler compute its output by inspecting the
rules. `source` checks every constructor against `CDot.Typed` and `CDot.Subtyp`;
there are no target-typing premises hidden in this input judgment. This module
defines the full intended compiler domain, not a type-preservation theorem.
-/

namespace CDotFCCT.Core

open CDot

variable [Signature]

set_option autoImplicit true in
mutual
  /-- Core DOT typing derivations, including every non-inversion core rule. -/
  inductive Typing : Ctx → Trm → Typ → Type where
    | var : Env.Binds x T G → Typing G (.var x) T
    | allIntro (L : Vars) :
        (∀ z, z ∉ L → Typing (G.push z T) (t.open z) (U.open z)) →
        Typing G (.val (.lambda T t)) (.all T U)
    | allElim : Typing G (.path p) (.all S T) → Typing G (.path q) S →
        Typing G (.app p q) (T.openPath q)
    | newIntro (L : Vars) :
        (∀ z, z ∉ L →
          DefinitionsTyping z [] (G.push z (T.open z)) (ds.open z) (T.open z)) →
        (∀ z, z ∉ L →
          Typing (G.push z (T.open z)) (.path (.var z)) ((.path p A : Typ).open z)) →
        Typing G (.val (.new p A T ds)) (.bnd T)
    | newElim : Typing G (.path p) (.rcd (.trm a T)) →
        Typing G (.path (p.selectField a)) T
    | rcdIntro : Typing G (.path (p.selectField a)) T →
        Typing G (.path p) (.rcd (.trm a T))
    | letE (L : Vars) : Typing G t T →
        (∀ x, x ∉ L → Typing (G.push x T) (u.open x) U) →
        Typing G (.letE t u) U
    | sngl : Typing G (.path p) (.sngl q) → Typing G (.path q) T →
        Typing G (.path p) T
    | self : Typing G (.path p) T → Typing G (.path p) (.sngl p)
    | pathElim : Typing G (.path p) (.sngl q) →
        Typing G (.path (q.selectField a)) T →
        Typing G (.path (p.selectField a)) (.sngl (q.selectField a))
    | recIntro : Typing G (.path p) (T.openPath p) → Typing G (.path p) (.bnd T)
    | recElim : Typing G (.path p) (.bnd T) → Typing G (.path p) (T.openPath p)
    | andIntro : Typing G (.path p) T → Typing G (.path p) U →
        Typing G (.path p) (.and T U)
    | sub : Typing G t T → Subtyping G T U → Typing G t U

  /-- Definitions in recursive objects, including nested objects and path aliases. -/
  inductive DefinitionTyping : Var → Fields → Ctx → Def → Dec → Type where
    | typ : DefinitionTyping x fields G (.typ A T) (.typ A T T)
    | all : Typing G (.val (.lambda T t)) (.all U V) →
        DefinitionTyping x fields G (.trm b (.val (.lambda T t))) (.trm b (.all U V))
    | new (p : Path) : p = .select (.free x) fields → Typ.tightBounds (.bnd T) →
        DefinitionsTyping x (b :: fields) G (ds.openPath (p.selectField b))
          (T.openPath (p.selectField b)) →
        Typing G (.path (p.selectField b)) ((.path q A : Typ).openPath (p.selectField b)) →
        DefinitionTyping x fields G (.trm b (.val (.new q A T ds))) (.trm b (.bnd T))
    | path : Typing G (.path q) T →
        DefinitionTyping x fields G (.trm b (.path q)) (.trm b (.sngl q))

  /-- A complete object definition list with its native source intersection type. -/
  inductive DefinitionsTyping : Var → Fields → Ctx → Defs → Typ → Type where
    | one : DefinitionTyping x fields G d D →
        DefinitionsTyping x fields G (.cons .nil d) (.rcd D)
    | cons : DefinitionsTyping x fields G ds T → DefinitionTyping x fields G d D →
        ds.Hasnt d.label → DefinitionsTyping x fields G (.cons ds d) (.and T (.rcd D))

  /-- Core subtyping, including dependent arrows and both singleton-replacement directions. -/
  inductive Subtyping : Ctx → Typ → Typ → Type where
    | top : Subtyping G T .top
    | bot : Subtyping G .bot T
    | refl : Subtyping G T T
    | trans : Subtyping G S T → Subtyping G T U → Subtyping G S U
    | andLeft : Subtyping G (.and T U) T
    | andRight : Subtyping G (.and T U) U
    | andIntro : Subtyping G S T → Subtyping G S U → Subtyping G S (.and T U)
    | fld : Subtyping G T U → Subtyping G (.rcd (.trm a T)) (.rcd (.trm a U))
    | typ : Subtyping G S₂ S₁ → Subtyping G T₁ T₂ →
        Subtyping G (.rcd (.typ A S₁ T₁)) (.rcd (.typ A S₂ T₂))
    | snglPQ : Typing G (.path p) (.sngl q) → Typing G (.path q) U →
        ReplTyp p q T T' → Subtyping G T T'
    | snglQP : Typing G (.path p) (.sngl q) → Typing G (.path q) U →
        ReplTyp q p T T' → Subtyping G T T'
    | selLo : Typing G (.path p) (.rcd (.typ A S T)) → Subtyping G S (.path p A)
    | selHi : Typing G (.path p) (.rcd (.typ A S T)) → Subtyping G (.path p A) T
    | all (L : Vars) : Subtyping G S₂ S₁ →
        (∀ x, x ∉ L → Subtyping (G.push x S₂) (T₁.open x) (T₂.open x)) →
        Subtyping G (.all S₁ T₁) (.all S₂ T₂)
end

set_option autoImplicit false

mutual
  /-- Every compiler input is an actual source typing derivation. -/
  theorem Typing.source {G : Ctx} {t : Trm} {T : Typ} (h : Typing G t T) : Typed G t T :=
    match h with
    | .var lookup => .var lookup
    | .allIntro L body => .allIntro L (fun x fresh => (body x fresh).source)
    | .allElim function argument => .allElim function.source argument.source
    | .newIntro L fields tag => .newIntro L
        (fun x fresh => (fields x fresh).source) (fun x fresh => (tag x fresh).source)
    | .newElim object => .newElim object.source
    | .rcdIntro field => .rcdIntro field.source
    | .letE L rhs body => .letE L rhs.source (fun x fresh => (body x fresh).source)
    | .sngl equality value => .sngl equality.source value.source
    | .self value => .self value.source
    | .pathElim equality field => .pathElim equality.source field.source
    | .recIntro body => .recIntro body.source
    | .recElim object => .recElim object.source
    | .andIntro left right => .andIntro left.source right.source
    | .sub term sub => .sub term.source sub.source

  theorem DefinitionTyping.source {x : Var} {fields : Fields} {G : Ctx}
      {d : Def} {D : Dec} (h : DefinitionTyping x fields G d D) : TypedDef x fields G d D :=
    match h with
    | .typ => .typ
    | .all function => .all function.source
    | .new p equal tight fields tag => .new p equal tight fields.source tag.source
    | .path value => .path value.source

  theorem DefinitionsTyping.source {x : Var} {fields : Fields} {G : Ctx}
      {ds : Defs} {T : Typ} (h : DefinitionsTyping x fields G ds T) :
      TypedDefs x fields G ds T :=
    match h with
    | .one field => .one field.source
    | .cons fields field fresh => .cons fields.source field.source fresh

  theorem Subtyping.source {G : Ctx} {S T : Typ} (h : Subtyping G S T) : Subtyp G S T :=
    match h with
    | .top => .top
    | .bot => .bot
    | .refl => .refl
    | .trans left right => .trans left.source right.source
    | .andLeft => .andLeft
    | .andRight => .andRight
    | .andIntro left right => .andIntro left.source right.source
    | .fld field => .fld field.source
    | .typ lower upper => .typ lower.source upper.source
    | .snglPQ equality value replacement => .snglPQ equality.source value.source replacement
    | .snglQP equality value replacement => .snglQP equality.source value.source replacement
    | .selLo member => .selLo member.source
    | .selHi member => .selHi member.source
    | .all L param result => .all L param.source (fun x fresh => (result x fresh).source)
end

end CDotFCCT.Core
