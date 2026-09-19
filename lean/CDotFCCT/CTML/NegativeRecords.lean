import CDotFCCT.CTML.NegativeSelections
import CDotFCCT.CTML.ObservationRecords

/-!
# Refining native fields at an existing negative witness

The row layout and witness equivalences are retained explicitly. A field may be
strengthened to an already-opened, opaque member witness without creating a new
existential package. The strengthened row remains below its previous row, so any
old opaque supertype is retained as a native subtyping consequence.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.NegativeRecord

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation Coercion ObservationRecord

def mapFields (className : ClassName) (names : List FieldName) (unique : names.Nodup)
    (payload record : Term) : Term :=
  .record className (fields names unique fun name => lowerWitness payload (.proj record name))

theorem strengthenedTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth} {data witness lower upper answer : WFTy s.typeDepth}
    (negative : ∀ name ∈ names, NegativeWitness s answer (types name))
    (selected : NegativeWitness s answer witness) {field : FieldName} (member : field ∈ names)
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer))
    {payload record : Term} (hd : Recursive.HasType s context payload data)
    (hr : Recursive.HasType s context record (type className names types))
    (hl : Recursive.HasType s context (.proj record field) lower) :
    Recursive.HasType s context (mapFields className names unique payload record)
      (type className names (strengthen types field witness)) :=
  .record (fieldsTypingOverrideRecursive names unique _ types field _
    (fun name found => lowerWitnessRetainsRecursive (negative name found) hd
      (.projection (hr.subsumption (fieldType _ types found))))
    (lowerWitnessRefinementRecursive (negative field member) selected bound hd
      (.projection (hr.subsumption (fieldType _ types member))) hl))

def strengthenedWitnesses {s : SubtypingContext} {answer witness : WFTy s.typeDepth}
    {names : List FieldName} {types : FieldName → WFTy s.typeDepth}
    (negative : ∀ name ∈ names, NegativeWitness s answer (types name))
    (selected : NegativeWitness s answer witness) {field : FieldName} (member : field ∈ names)
    (name : FieldName) (found : name ∈ names) :
    NegativeWitness s answer (strengthen types field witness name) := by
  by_cases equal : name = field
  · simpa [strengthen, equal] using (negative field member).intersection selected
  · simpa [strengthen, equal] using negative name found

theorem refinement {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth}
    {data witness lower upper answer original : WFTy s.typeDepth}
    (negative : ∀ name ∈ names, NegativeWitness s answer (types name))
    (selected : NegativeWitness s answer witness) {field : FieldName} (member : field ∈ names)
    (old : Subtype s (type className names types) original)
    (bound : Subtype s (preciseMember data witness answer) (memberView lower upper answer))
    {payload record : Term} (hd : Recursive.HasType s context payload data)
    (hr : Recursive.HasType s context record (type className names types))
    (hl : Recursive.HasType s context (.proj record field) lower) :
    Recursive.HasType s context (mapFields className names unique payload record)
      (WFTy.intersection original (WFTy.record field witness)) :=
  let refined := strengthenedTyping unique negative selected member bound hd hr hl
  .intersection
    (refined.subsumption (.trans (strengthenLe className names types field witness) old))
    (refined.subsumption (strengthenField className types member witness))

/-- Strengthening a field can precede opening the selected member's package consumer. -/
theorem strengthenedSelectionTyping {s : SubtypingContext}
    {context : TypingContext s.typeDepth} {className : ClassName} {names : List FieldName}
    (unique : names.Nodup) {types : FieldName → WFTy s.typeDepth}
    {data carrier lower upper answer : WFTy s.typeDepth}
    (negative : ∀ name ∈ names, NegativeWitness s answer (types name))
    {field : FieldName} (member : field ∈ names)
    (bound : Subtype s carrier (memberView lower upper answer)) {payload record : Term}
    (hd : Recursive.HasType s context payload data)
    (hr : Recursive.HasType s context record (type className names types))
    (hl : Recursive.HasType s context (.proj record field) lower) :
    Recursive.HasType s context (mapFields className names unique payload record)
      (type className names (strengthen types field (negativeSelector data carrier answer))) :=
  .record (fieldsTypingOverrideRecursive names unique _ types field _
    (fun name found => lowerWitnessRetainsRecursive (negative name found) hd
      (.projection (hr.subsumption (fieldType _ types found))))
    (lowerWitness_selectRefinementRecursive (negative field member) bound hd
      (.projection (hr.subsumption (fieldType _ types member))) hl))

def strengthenedSelectionWitnesses {s : SubtypingContext}
    {data carrier answer : WFTy s.typeDepth} {names : List FieldName}
    {types : FieldName → WFTy s.typeDepth}
    (negative : ∀ name ∈ names, NegativeWitness s answer (types name))
    {field : FieldName} (member : field ∈ names) (name : FieldName) (found : name ∈ names) :
    NegativeWitness s answer (strengthen types field (negativeSelector data carrier answer) name) :=
  strengthenedWitnesses negative (.ofView (negativeSelectorView data carrier answer))
    member name found

theorem selectionRefinement {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth}
    {data carrier lower upper answer original : WFTy s.typeDepth}
    (negative : ∀ name ∈ names, NegativeWitness s answer (types name))
    {field : FieldName} (member : field ∈ names)
    (old : Subtype s (type className names types) original)
    (bound : Subtype s carrier (memberView lower upper answer)) {payload record : Term}
    (hd : Recursive.HasType s context payload data)
    (hr : Recursive.HasType s context record (type className names types))
    (hl : Recursive.HasType s context (.proj record field) lower) :
    Recursive.HasType s context (mapFields className names unique payload record)
      (WFTy.intersection original (WFTy.record field (negativeSelector data carrier answer))) :=
  let refined := strengthenedSelectionTyping unique negative member bound hd hr hl
  .intersection
    (refined.subsumption
      (.trans (strengthenLe className names types field
        (negativeSelector data carrier answer)) old))
    (refined.subsumption (strengthenField className types member _))

theorem mapFieldsValue (className : ClassName) (names : List FieldName) (unique : names.Nodup)
    (payload record : Term) : Value (mapFields className names unique payload record) :=
  .record _ _ (fieldsAllValues names unique _ (fun _ _ => .abs _))

theorem projectExecution {className : ClassName} {names : List FieldName}
    (unique : names.Nodup) {field : FieldName} (member : field ∈ names)
    {payload record value continuation : Term}
    (hd : Value payload) (lookup : Steps (.proj record field) value) (hv : Value value)
    (hk : Value continuation) :
    Steps (.app (.proj (mapFields className names unique payload record) field) continuation)
      (.app value continuation) :=
  .trans (.appHead _ (.proj (mapFieldsValue _ _ unique _ _) (fieldsLookup unique _ member)))
    (lowerWitness_stepsOfInput hd lookup hv hk)

theorem projectReturns {className : ClassName} {names : List FieldName}
    (unique : names.Nodup) {field : FieldName} (member : field ∈ names)
    {payload record value result : Term} (hd : Value payload)
    (lookup : Steps (.proj record field) value) (hv : Value value)
    (returns : Returns value result) :
    Returns (.proj (mapFields className names unique payload record) field) result :=
  fun _ hk => (projectExecution unique member hd lookup hv hk).trans' (returns _ hk)

end CDotFCCT.CTML.NegativeRecord
