(*
This file mechanizes the EncodeType function in Coq.
It can be used to convert types from the mechanized source calculus into iDOT.
*)
Require Import Helpers.
Require Import Library.
(*
*** Warning: in file Predefs.v,
    required library Definitions matches several files in path
    (found Definitions.v in ../lambda2Gmu and ../../dot-calculus/src/extensions/paths; used the latter)
 *)

Definition type_map := nat -> nat * typ_label.
Definition empty_map : type_map := fun x => (x, GenT).
Definition skip1 : type_map -> type_map :=
  fun f x =>
    let (n, l) := f x in
    (1 + n, l).
Definition open1 : type_map -> typ_label -> type_map :=
  fun f l x =>
    match x with
    | 0 => (0, l)
    | S n =>
      let (n', l') := f n in
      (n' + 1, l')
    end.

Fixpoint translateType
         (T : Source.typ)
         (ty_map : type_map)
         {struct T}
  : Target.typ :=
  match T with
  | typ_bvar J =>
    let (n, l) := ty_map J in
    (ref n) ↓ l
  | typ_fvar X =>
    typ_path (pvar X) GenT
  | typ_unit =>
    (pvar lib) ↓ Unit
  | T1 ** T2 =>
    let T1' := translateType T1 ty_map in
    let T2' := translateType T2 ty_map in
    TupleT T1' T2'
  | T1 ==> T2 =>
    let T1' := translateType T1 ty_map in
    let T2' := translateType T2 (skip1 ty_map) in
    typ_all T1' T2'
  | Source.typ_all T =>
    let T1 := translateType T (open1 ty_map GenT) in
    typ_all GenArgT T1
  | typ_gadt Ts g =>
    let Ts' := List.map (fun t => translateType t ty_map) Ts in
    let base := pvar env ↓ (GN g) in
    let res :=
        List.fold_left
          (fun acc T => match acc with
                     | (i, rest) =>
                       (
                         1+i,
                         (rest ∧ typ_rcd { Ai i == T })
                       )
                     end)
          Ts'
          (1, base) in
    snd res
  end.

Definition translateTyp0 (T : Source.typ) : Target.typ := translateType T empty_map.
