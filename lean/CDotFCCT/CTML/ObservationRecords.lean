import CDotFCCT.CTML.ObservationViews

/-!
# Refining a suspended field while retaining a precise native record

The complete field layout is explicit. Each field stores an observation, as in
the runtime CPS pass. Mapping the identity conversion over those observations
preserves the original record type and can add a selector view to one field.
An opaque supertype is retained through the original precise record type.

This module does not infer a precise layout from an arbitrary opaque type. The
general compiler still has to maintain that layout and the shared member carrier.
-/

set_option autoImplicit false

namespace CDotFCCT.CTML.ObservationRecord

open CTMLCore CTMLCore.Syntax CTMLCore.Evaluation Coercion

def fields : (names : List FieldName) → names.Nodup → (FieldName → Term) → TermFields names
  | [], _, _ => .nil
  | name :: names, unique, values =>
      .cons name (values name) (fields names (List.nodup_cons.mp unique).2 values)
        (List.nodup_cons.mp unique).1

def type {n : Nat} (className : ClassName) (names : List FieldName)
    (types : FieldName → WFTy n) : WFTy n :=
  recordResultType className (names.map fun name => (name, types name))

private theorem foldLeStart (s : SubtypingContext)
    (entries : List (FieldName × WFTy s.typeDepth)) (start : WFTy s.typeDepth) :
    Subtype s
      (entries.foldl (fun result entry => WFTy.intersection result
        (WFTy.record entry.1 entry.2)) start) start :=
  match entries with
  | [] => .refl
  | _ :: entries => .trans (foldLeStart s entries _) .interLeft

private theorem foldLeField (s : SubtypingContext)
    {entries : List (FieldName × WFTy s.typeDepth)} {name : FieldName}
    {fieldType : WFTy s.typeDepth} (member : (name, fieldType) ∈ entries)
    (start : WFTy s.typeDepth) :
    Subtype s
      (entries.foldl (fun result entry => WFTy.intersection result
        (WFTy.record entry.1 entry.2)) start) (WFTy.record name fieldType) := by
  induction member generalizing start with
  | head rest => exact .trans (foldLeStart s rest _) .interRight
  | tail _ _ ih => exact ih _

theorem fieldType {s : SubtypingContext} (className : ClassName)
    {names : List FieldName} (types : FieldName → WFTy s.typeDepth)
    {name : FieldName} (member : name ∈ names) :
    Subtype s (type className names types) (WFTy.record name (types name)) :=
  foldLeField s (List.mem_map.mpr ⟨name, member, rfl⟩) _

private theorem foldMono (s : SubtypingContext) (names : List FieldName)
    (first second : FieldName → WFTy s.typeDepth) (left right : WFTy s.typeDepth)
    (start : Subtype s left right)
    (pointwise : ∀ name ∈ names, Subtype s (first name) (second name)) :
    Subtype s
      ((names.map fun name => (name, first name)).foldl
        (fun result entry => WFTy.intersection result (WFTy.record entry.1 entry.2)) left)
      ((names.map fun name => (name, second name)).foldl
        (fun result entry => WFTy.intersection result (WFTy.record entry.1 entry.2)) right) :=
  match names with
  | [] => start
  | name :: names =>
      foldMono s names first second _ _
        (.interMono start (.record (pointwise name List.mem_cons_self)))
        (fun field member => pointwise field (List.mem_cons_of_mem _ member))

theorem mono {s : SubtypingContext} (className : ClassName) (names : List FieldName)
    {first second : FieldName → WFTy s.typeDepth}
    (pointwise : ∀ name ∈ names, Subtype s (first name) (second name)) :
    Subtype s (type className names first) (type className names second) :=
  foldMono s names first second _ _ .refl pointwise

def strengthen {n : Nat} (types : FieldName → WFTy n) (field : FieldName) (added : WFTy n)
    (name : FieldName) : WFTy n :=
  if name = field then WFTy.intersection (types field) added else types name

theorem strengthenLe {s : SubtypingContext} (className : ClassName) (names : List FieldName)
    (types : FieldName → WFTy s.typeDepth) (field : FieldName) (added : WFTy s.typeDepth) :
    Subtype s (type className names (strengthen types field added))
      (type className names types) := by
  refine mono className names ?_
  intro name _
  by_cases equal : name = field
  · simpa [strengthen, equal] using
      (Subtype.interLeft (context := s) (left := types field) (right := added))
  · simpa [strengthen, equal] using (CTMLCore.Subtype.refl (context := s) (type := types name))

def strengthenShapes {n : Nat} {names : List FieldName} {types : FieldName → WFTy n}
    {answer : WFTy n} (shapes : ∀ name ∈ names, Observation answer (types name))
    {field : FieldName} (member : field ∈ names) {added : WFTy n}
    (shape : Observation answer added) (name : FieldName) (found : name ∈ names) :
    Observation answer (strengthen types field added name) := by
  by_cases equal : name = field
  · simpa [strengthen, equal] using Observation.both (shapes field member) shape
  · simpa [strengthen, equal] using shapes name found

theorem strengthenField {s : SubtypingContext} (className : ClassName)
    {names : List FieldName} (types : FieldName → WFTy s.typeDepth)
    {field : FieldName} (member : field ∈ names) (added : WFTy s.typeDepth) :
    Subtype s (type className names (strengthen types field added)) (WFTy.record field added) := by
  have found : Subtype s (type className names (strengthen types field added))
      (WFTy.record field (WFTy.intersection (types field) added)) := by
    simpa [strengthen] using fieldType (s := s) className (strengthen types field added) member
  exact .trans found (.record .interRight)

theorem fieldsTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (names : List FieldName) (unique : names.Nodup) (values : FieldName → Term)
    (types : FieldName → WFTy s.typeDepth)
    (typing : ∀ name ∈ names, HasType s context (values name) (types name)) :
    FieldsHaveType s context (fields names unique values)
      (names.map fun name => (name, types name)) :=
  match names with
  | [] => .nil
  | name :: names =>
      .cons (typing name List.mem_cons_self)
        (fieldsTyping names (List.nodup_cons.mp unique).2 values types
          (fun field member => typing field (List.mem_cons_of_mem _ member)))

def mapLowerFields (className : ClassName) (names : List FieldName) (unique : names.Nodup)
    (payload record : Term) : Term :=
  .record className (fields names unique fun name => mapLower payload (.proj record name))

theorem retain {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth} {data answer : WFTy s.typeDepth}
    (shapes : ∀ name ∈ names, Observation answer (types name))
    {payload record : Term} (hd : HasType s context payload data)
    (hr : HasType s context record (type className names types)) :
    HasType s context (mapLowerFields className names unique payload record)
      (type className names types) :=
  .record (fieldsTyping names unique _ types fun name member =>
    (shapes name member).retain hd (.projection (hr.subsumption (fieldType _ types member))))

theorem fieldsTyping_override {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (names : List FieldName) (unique : names.Nodup) (values : FieldName → Term)
    (types : FieldName → WFTy s.typeDepth) (field : FieldName) (added : WFTy s.typeDepth)
    (typing : ∀ name ∈ names, HasType s context (values name) (types name))
    (selected : HasType s context (values field) added) :
    FieldsHaveType s context (fields names unique values)
      (names.map fun name => (name, if name = field then added else types name)) := by
  refine fieldsTyping names unique values _ ?_
  intro name member
  split_ifs with equal
  · simpa only [equal] using selected
  · exact typing name member

/-- Expose the strengthened precise row so that later refinements can retain it too. -/
theorem strengthenedTyping {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth} {data carrier lower upper answer : WFTy s.typeDepth}
    (shapes : ∀ name ∈ names, Observation answer (types name))
    {field : FieldName} (member : field ∈ names)
    (bound : Subtype s carrier (memberView lower upper answer))
    {payload record : Term} (hd : HasType s context payload data)
    (hr : HasType s context record (type className names types))
    (selected : HasType s context (.proj record field) (observation lower answer)) :
    HasType s context (mapLowerFields className names unique payload record)
      (type className names (strengthen types field (selector data carrier answer))) :=
  .record (fieldsTyping_override names unique (fun name => mapLower payload (.proj record name))
    types field _
    (fun name found => (shapes name found).retain hd
      (.projection (hr.subsumption (fieldType _ types found))))
    (mapLower_refinement (shapes field member) bound hd
      (.projection (hr.subsumption (fieldType _ types member))) selected))

theorem selectorField {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth} {data carrier lower upper answer : WFTy s.typeDepth}
    (shapes : ∀ name ∈ names, Observation answer (types name))
    {field : FieldName} (member : field ∈ names)
    (bound : Subtype s carrier (memberView lower upper answer))
    {payload record : Term} (hd : HasType s context payload data)
    (hr : HasType s context record (type className names types))
    (selected : HasType s context (.proj record field) (observation lower answer)) :
    HasType s context (mapLowerFields className names unique payload record)
      (WFTy.record field (selector data carrier answer)) :=
  (strengthenedTyping unique shapes member bound hd hr selected).subsumption
    (strengthenField className types member _)

/-- The old view may be opaque; its proof comes from the retained precise row. -/
theorem refinement {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth}
    {data carrier lower upper answer original : WFTy s.typeDepth}
    (shapes : ∀ name ∈ names, Observation answer (types name))
    {field : FieldName} (member : field ∈ names)
    (old : Subtype s (type className names types) original)
    (bound : Subtype s carrier (memberView lower upper answer))
    {payload record : Term} (hd : HasType s context payload data)
    (hr : HasType s context record (type className names types))
    (selected : HasType s context (.proj record field) (observation lower answer)) :
    HasType s context (mapLowerFields className names unique payload record)
      (WFTy.intersection original (WFTy.record field (selector data carrier answer))) :=
  .intersection ((retain unique shapes hd hr).subsumption old)
    (selectorField unique shapes member bound hd hr selected)

theorem fieldsTypingRecursive {s : SubtypingContext} {context : TypingContext s.typeDepth}
    (names : List FieldName) (unique : names.Nodup) (values : FieldName → Term)
    (types : FieldName → WFTy s.typeDepth)
    (typing : ∀ name ∈ names, Recursive.HasType s context (values name) (types name)) :
    Recursive.FieldsHaveType s context (fields names unique values)
      (names.map fun name => (name, types name)) :=
  match names with
  | [] => .nil
  | name :: names =>
      .cons (typing name List.mem_cons_self)
        (fieldsTypingRecursive names (List.nodup_cons.mp unique).2 values types
          (fun field member => typing field (List.mem_cons_of_mem _ member)))

theorem retainRecursive {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth} {data answer : WFTy s.typeDepth}
    (shapes : ∀ name ∈ names, Observation answer (types name))
    {payload record : Term} (hd : Recursive.HasType s context payload data)
    (hr : Recursive.HasType s context record (type className names types)) :
    Recursive.HasType s context (mapLowerFields className names unique payload record)
      (type className names types) :=
  .record (fieldsTypingRecursive names unique _ types fun name member =>
    (shapes name member).retainRecursive hd
      (.projection (hr.subsumption (fieldType _ types member))))

theorem fieldsTypingOverrideRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth}
    (names : List FieldName) (unique : names.Nodup) (values : FieldName → Term)
    (types : FieldName → WFTy s.typeDepth) (field : FieldName) (added : WFTy s.typeDepth)
    (typing : ∀ name ∈ names, Recursive.HasType s context (values name) (types name))
    (selected : Recursive.HasType s context (values field) added) :
    Recursive.FieldsHaveType s context (fields names unique values)
      (names.map fun name => (name, if name = field then added else types name)) := by
  refine fieldsTypingRecursive names unique values _ ?_
  intro name member
  split_ifs with equal
  · simpa only [equal] using selected
  · exact typing name member

theorem strengthenedTypingRecursive {s : SubtypingContext}
    {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth} {data carrier lower upper answer : WFTy s.typeDepth}
    (shapes : ∀ name ∈ names, Observation answer (types name))
    {field : FieldName} (member : field ∈ names)
    (bound : Subtype s carrier (memberView lower upper answer))
    {payload record : Term} (hd : Recursive.HasType s context payload data)
    (hr : Recursive.HasType s context record (type className names types))
    (selected : Recursive.HasType s context (.proj record field) (observation lower answer)) :
    Recursive.HasType s context (mapLowerFields className names unique payload record)
      (type className names (strengthen types field (selector data carrier answer))) :=
  .record (fieldsTypingOverrideRecursive names unique
    (fun name => mapLower payload (.proj record name)) types field _
    (fun name found => (shapes name found).retainRecursive hd
      (.projection (hr.subsumption (fieldType _ types found))))
    (mapLower_refinementRecursive (shapes field member) bound hd
      (.projection (hr.subsumption (fieldType _ types member))) selected))

theorem selectorFieldRecursive {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth} {data carrier lower upper answer : WFTy s.typeDepth}
    (shapes : ∀ name ∈ names, Observation answer (types name))
    {field : FieldName} (member : field ∈ names)
    (bound : Subtype s carrier (memberView lower upper answer))
    {payload record : Term} (hd : Recursive.HasType s context payload data)
    (hr : Recursive.HasType s context record (type className names types))
    (selected : Recursive.HasType s context (.proj record field) (observation lower answer)) :
    Recursive.HasType s context (mapLowerFields className names unique payload record)
      (WFTy.record field (selector data carrier answer)) :=
  (strengthenedTypingRecursive unique shapes member bound hd hr selected).subsumption
    (strengthenField className types member _)

theorem refinementRecursive {s : SubtypingContext} {context : TypingContext s.typeDepth}
    {className : ClassName} {names : List FieldName} (unique : names.Nodup)
    {types : FieldName → WFTy s.typeDepth}
    {data carrier lower upper answer original : WFTy s.typeDepth}
    (shapes : ∀ name ∈ names, Observation answer (types name))
    {field : FieldName} (member : field ∈ names)
    (old : Subtype s (type className names types) original)
    (bound : Subtype s carrier (memberView lower upper answer))
    {payload record : Term} (hd : Recursive.HasType s context payload data)
    (hr : Recursive.HasType s context record (type className names types))
    (selected : Recursive.HasType s context (.proj record field) (observation lower answer)) :
    Recursive.HasType s context (mapLowerFields className names unique payload record)
      (WFTy.intersection original (WFTy.record field (selector data carrier answer))) :=
  .intersection ((retainRecursive unique shapes hd hr).subsumption old)
    (selectorFieldRecursive unique shapes member bound hd hr selected)

theorem fieldsAllValues (names : List FieldName) (unique : names.Nodup)
    (values : FieldName → Term) (valid : ∀ name ∈ names, Value (values name)) :
    TermFields.AllValues (fields names unique values) :=
  match names with
  | [] => .nil
  | name :: names =>
      .cons (valid name List.mem_cons_self)
        (fieldsAllValues names (List.nodup_cons.mp unique).2 values
          (fun field member => valid field (List.mem_cons_of_mem _ member)))

theorem fieldsLookup {names : List FieldName} (unique : names.Nodup)
    (values : FieldName → Term) {name : FieldName} (member : name ∈ names) :
    TermFields.Lookup (fields names unique values) name (values name) := by
  induction member with
  | head _ => exact .here
  | tail _ _ ih => exact .there (ih (List.nodup_cons.mp unique).2)

/-- Rebuilding the row keeps every computation suspended. -/
theorem mapLowerFieldsValue (className : ClassName) (names : List FieldName)
    (unique : names.Nodup) (payload record : Term) :
    Value (mapLowerFields className names unique payload record) :=
  .record _ _ (fieldsAllValues names unique _ (fun _ _ => .abs _))

/-- Every field still passes the same value to its continuation. -/
theorem projectReturns {className : ClassName} {names : List FieldName}
    (unique : names.Nodup) {field : FieldName} (member : field ∈ names)
    {payload record result : Term} (hd : Value payload) (hv : Value result)
    (old : Returns (.proj record field) result) :
    Returns (.proj (mapLowerFields className names unique payload record) field) result :=
  fun continuation hk => .trans
    (.appHead _ (.proj (mapLowerFieldsValue _ _ unique _ _)
      (fieldsLookup unique _ member)))
    (old.mapLower hd hv continuation hk)

end CDotFCCT.CTML.ObservationRecord
