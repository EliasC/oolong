Require Export ListExtras.
Require Export CpdtTactics.
Require Export LibTactics.
Require Export Omega.

Tactic Notation "inv" hyp(H) "as" simple_intropattern(l) := inversion H as l; subst; clear H.
Tactic Notation "inv" hyp(H) := inversion H; subst; clear H.

Ltac inv_eq :=
  match goal with
    | [H : ?e _ = ?e _ |- _] =>
      inv H
    | [H : ?e _ _ = ?e _ _ |- _] =>
      inv H
    | [H : ?e _ _ _ = ?e _ _ _ |- _] =>
      inv H
    | [H : ?e _ _ _ _ = ?e _ _ _ _ |- _] =>
      inv H
    | [H : ?e _ _ _ _ _ = ?e _ _ _ _ _ |- _] =>
      inv H
    | [H : ?e _ _ _ _ _ _ = ?e _ _ _ _ _ _ |- _] =>
      inv H
    | [H : ?e _ _ _ _ _ _ _ = ?e _ _ _ _ _ _ _ |- _] =>
      inv H
    | _ => fail 1 "No invertable equalities in context"
  end; auto 2.

Ltac rewrite_and_invert :=
  match goal with
    | [H1 : ?X = ?Y, H2 : ?X = ?Z |- _ ] =>
      rewrite H1 in H2; inv H2; simpl; auto 2
    | _ => fail 1 "No matching invertable equalities in context"
  end.

Ltac ex_falso_quodlibet :=
  match goal with
    | [H : False |- _] =>
      inversion H
  end.

Ltac contra :=
  match goal with
    | [ |- ~ _] => intros contra; inv contra
    | [_ : _ |- ~ _] => intros contra; inv contra
    | [ |- _ <> _] => intros contra; inv contra
    | [_ : _ |- _ <> _] => intros contra; inv contra
    | _ => fail 1 "Goal is not a negation"
  end.

Ltac option_inv :=
  match goal with
    | [H : Some _ = None |- _] => congruence
    | [H : None = Some _ |- _] => congruence
    | [H : None <> None |- _] => congruence
    | [H : Some ?x <> Some ?x |- _] => congruence
    | _ => fail 1 "No equalities of option types in context"
  end.

Hint Extern 1 => option_inv.

(* Cases, by Aaron Bohannon *)

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Require String. Open Scope string_scope.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
