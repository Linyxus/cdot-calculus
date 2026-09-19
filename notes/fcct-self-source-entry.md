# Source entry for the solved self-field constructor

`CarrierRuntimeSelfSource.compile` takes an actual `Core.Typing` derivation and
its CPS answer type. It recognizes one object with the complete source shape
`new tag.Tag { a : self.type } { a = self }` and checks that the requested source
result is exactly its recursive object type. Other syntax or result types return
`none`.

The pass computes the standard carrier support
`[Slot.payload, Slot.present a, Slot.child a]`. Its presence witness is `Top`;
the child witness is the solved carrier itself; the payload is the thunk of the
solved ordinary row. The object has no source type-member definitions. Its tag
member remains checked in the source derivation and is erased by the runtime
pass, so it needs no runtime member slot here.

The result contains a target typing derivation for the exact `TermCPS.compile`
output, using the standard generated ordinary field names. It obtains all target
witnesses and constraints from `CarrierRuntimeSelf`; callers provide no target
bounds, equations, layouts or typing proofs. The result is closed because the
only runtime path in this source shape is its bound self path. The source context
may still contain the free tag variable.

The checked regression derives the source object in a context containing
`tag : { Tag : Top .. Top }`, constructs the compiler result by reduction, verifies
the generated slot list and exact emitted term, and obtains target safety from
the returned derivation. A source derivation subsumed to `Top` is rejected by the
result-type check.

The target result is the specialized solved self-object interface. This is an
actual narrow derivation-to-derivation entry, not a general recursive-object
`CarrierTranslation.TypeCode` theorem. Uniform translation of arbitrary result
annotations, ambient member dependencies, additional fields or field clients
remains separate work. This file does not claim that the complete core-DOT
compiler is finished.
