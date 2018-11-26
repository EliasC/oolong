Require Coq.Setoids.Setoid.
Require Import Coq.Arith.Peano_dec.
Require Import Coq.Arith.EqNat.

Require Import Shared.
Require Import Meta.

(*
=============
Partial maps
=============
*)

Ltac case_id_eq_dec :=
  match goal with
    | _ : _ |- context[id_eq_dec _ _] =>
      repeat(elim id_eq_dec); intros; subst; try(congruence)
  end.

Ltac case_extend :=
  match goal with
    | _ : _ |- context[extend _ _ _ _] =>
      unfold extend; case_id_eq_dec
  end.

Ltac case_drop :=
  match goal with
    | _ : _ |- context[drop _ _ _] =>
      unfold drop; cases_if
  end.

Lemma extend_eq :
  forall A B (eqd : ID A) Gamma x y (v : B),
    x = y ->
    extend Gamma x v y = Some v.
Proof with case_extend.
  introv...
Qed.

Hint Resolve extend_eq.

Lemma extend_neq :
  forall A B (eqd : ID A) Gamma x y (v : B),
    x <> y ->
    extend Gamma x v y = Gamma y.
Proof with case_extend.
  introv...
Qed.

Hint Resolve extend_neq.

Lemma extend_order :
  forall A B (eqd : ID A) Gamma x y z (v1 v2 : B),
    x <> y ->
    extend (extend Gamma x v1) y v2 z =
    extend (extend Gamma y v2) x v1 z.
Proof with case_extend.
  introv...
Qed.

Hint Resolve extend_order.

Lemma extend_shadow :
  forall A B (eqd : ID A) Gamma x y (v1 v2 : B),
    extend (extend Gamma x v1) x v2 y=
    extend Gamma x v2 y.
Proof with case_extend.
  introv...
Qed.

Hint Resolve extend_shadow.