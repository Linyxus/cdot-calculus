import CDot.Substitution

/-! # Derived replacement rules used by inversion proofs -/

namespace CDot

variable [Signature]

theorem TightSubtyp.snglPQLeft {G : Ctx} {p q : Path} {S S' T U : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q U)
    (hst : TightSubtyp G S T) (hr : ReplTyp p q S S') :
    TightSubtyp G S' T :=
  .trans (.snglQP hp hq hr.swap) hst

theorem TightSubtyp.snglPQRight {G : Ctx} {p q : Path} {S T T' U : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q U)
    (hst : TightSubtyp G S T) (hr : ReplTyp p q T T') :
    TightSubtyp G S T' :=
  .trans hst (.snglPQ hp hq hr)

theorem TightSubtyp.snglQPLeft {G : Ctx} {p q : Path} {S S' T U : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q U)
    (hst : TightSubtyp G S T) (hr : ReplTyp q p S S') :
    TightSubtyp G S' T :=
  .trans (.snglPQ hp hq hr.swap) hst

theorem TightSubtyp.snglQPRight {G : Ctx} {p q : Path} {S T T' U : Typ}
    (hp : PreciseTyping3 G p (.sngl q)) (hq : PreciseTyping3 G q U)
    (hst : TightSubtyp G S T) (hr : ReplTyp q p T T') :
    TightSubtyp G S T' :=
  .trans hst (.snglQP hp hq hr)

end CDot
