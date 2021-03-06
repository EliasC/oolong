Require Coq.Bool.Sumbool.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.

Require Import Shared.

(*
====
IDs
====
*)

Class ID (A : Type) :=
{
  id_eq_dec : forall (x y : A), {x = y} + {x <> y}
}.

Instance ID_nat : ID nat := {}.
  repeat decide equality.
Qed.

Inductive svar : Type :=
  | SVar : nat -> svar.

Instance ID_svar : ID svar := {}.
  repeat decide equality.
Qed.

Definition this := SVar 0.

Inductive dvar : Type :=
  | DVar : nat -> dvar.

Instance ID_dvar : ID dvar := {}.
  repeat decide equality.
Qed.

Definition field_id := nat.
Definition method_id := nat.
Definition class_id := nat.
Definition interface_id := nat.
Definition loc := nat.
Definition lock := loc%type.

(*
====
Map
====
*)

Definition partial_map (from:Type) {eqd : ID from} (to:Type) := from -> option to.

Definition empty {A B:Type} {eqd : ID A} : partial_map A B := (fun _ => None).

Definition extend {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) (b:B) :=
  fun a' => if id_eq_dec a a' then
              Some b
            else
              Gamma a'.

Hint Unfold extend.

Definition drop {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) :=
  fun a' => if id_eq_dec a a' then
              None
            else
              Gamma a'.

Hint Unfold drop.

Definition fresh {A B:Type} {eqd : ID A} (Gamma : partial_map A B) (a:A) := Gamma a = None.

Hint Unfold fresh.
