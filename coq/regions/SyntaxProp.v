Require Import List.

Require Export Syntax.
Require Export MetaProp.
Require Import Shared.

Ltac destruct_var :=
  match goal with
    | [v : var |- _] => destruct v as [[]|[]]
    | _ => fail 1 "No var in context"
  end.

Ltac unfold_ctx :=
  match goal with
    | [H: context[ctx_call] |- _] => unfold ctx_call in H
    | [_ : _ |- context[ctx_call]] => unfold ctx_call
    | [H: context[ctx_update] |- _] => unfold ctx_update in H
    | [_ : _ |- context[ctx_update]] => unfold ctx_update
    | [H: context[ctx_let] |- _] => unfold ctx_let in H
    | [_ : _ |- context[ctx_let]] => unfold ctx_let
    | [H: context[ctx_cast] |- _] => unfold ctx_cast in H
    | [_ : _ |- context[ctx_cast]] => unfold ctx_cast
    | [H: context[ctx_locked] |- _] => unfold ctx_locked in H
    | [_ : _ |- context[ctx_locked]] => unfold ctx_locked
    | _ => idtac
  end.

Ltac malformed_context :=
  match goal with
    | [Hctx : is_econtext ?ctx |- _] => inv Hctx; repeat(unfold_ctx); try(congruence)
    | _ => fail 1 "could not prove malformed context"
  end.

Ltac lookup_in x :=
  let HIn := fresh "HIn" in
  match goal with
    | [Hlookup : ?lookup (?l, _, _) _ = Some x |- _] =>
      assert (HIn : In x l) by (unfold lookup in Hlookup; eapply find_in; eassumption)
    | [Hlookup : ?lookup (_, ?l, _) _ = Some x |- _] =>
      assert (HIn : In x l) by (unfold lookup in Hlookup; eapply find_in; eassumption)
    | [Hlookup : ?lookup ?l _ = Some x |- _] =>
      assert (HIn : In x l) by (unfold lookup in Hlookup; eapply find_in; eassumption)
    | _ => fail "No lookup in premise"
  end.

Ltac in_forall x name :=
  match goal with
    | [H : Forall ?P ?l,
       HIn : In x ?l |- _] =>
      assert (name: P x) by (rewrite Forall_forall in H; apply H; apply HIn)
    | _ => fail "No Forall in premise"
  end.

Ltac lookup_forall' x name :=
  lookup_in x; in_forall x name.

Ltac lookup_forall val name :=
  let x := fresh in
  remember val as x; lookup_forall' x name;
  subst.

Ltac lookup_forall_auto name :=
  match goal with
    | [H : ?lookup _ _ = Some ?val |- _] =>
      lookup_forall val name
  end.

Tactic Notation "lookup_forall" constr(val) "as" ident(name) := lookup_forall val name.

Tactic Notation "lookup_forall" "as" ident(name) := lookup_forall_auto name.

Tactic Notation "solve" "by" "lookup_forall" :=
  let H := fresh in solve[lookup_forall_auto H; inv H; eauto].


(*
=========
econtext
=========
*)

Lemma econtext_freeVars :
  forall ctx e e',
    is_econtext ctx ->
    freeVars e = nil ->
    ctx e' = e ->
    freeVars e' = nil.
Proof with crush.
  introv Hctx Hfree Heq.
  induction Hctx; intros;
  subst;
  try(destruct_var)...
  apply app_eq_nil in Hfree...
Qed.


(*
=========
subst
=========
*)

Lemma locks_subst :
  forall e x y,
    locks e = locks (subst x y e).
Proof with eauto.
  intros.
  induction e; simpl; repeat(destruct_var); try(cases_if); crush...
Qed.

Lemma no_locks_subst :
  forall e x y,
    no_locks e ->
    no_locks (subst x y e).
Proof with eauto.
  introv noL.
  inverts noL as noW noR.
  rewrite locks_subst with e x y in noW.
  unfold no_locks...
Qed.

(*
=========
freeVars
=========
*)

Lemma freeVars_subst :
  forall x y e,
    freeVars (subst x y e) =
    List.remove id_eq_dec x (freeVars e).
Proof with auto.
  intros. induction e;
  repeat(destruct_var); simpl; autounfold;
  repeat(elim id_eq_dec; intros; subst; simpl);
  try(rewrite IHe);
  try(rewrite IHe1);
  try(rewrite IHe2);
  try(rewrite IHe3);
  repeat(rewrite remove_app);
  try(rewrite remove_idempotence);
  try(rewrite remove_commutative)...
Qed.

Hint Rewrite freeVars_subst : freeVars.


(*
=======
Lookup
=======
*)

Lemma classLookup_not_none :
  forall P c,
    classLookup P c <> None ->
    exists i fs ms, classLookup P c = Some (Cls c i fs ms).
Proof with eauto.
  intros [[cs ?] ?] c Hlookup.
  unfold classLookup in Hlookup. apply find_notNone in Hlookup.
  destruct Hlookup as [[c' fs ms] Hfind].
  assert (Heq : c = c') by
      (apply find_true in Hfind;
       apply beq_nat_eq; auto).
  subst...
Qed.

Lemma interfaceLookup_not_none :
  forall P i,
    interfaceLookup P i <> None ->
    (exists msigs, interfaceLookup P i = Some (Interface i msigs))
    \/ (exists i1 i2, interfaceLookup P i = Some (ExtInterface i i1 i2)).
Proof with eauto.
  intros [[? ids] ?] i Hlookup.
  unfold interfaceLookup in Hlookup.
  apply find_notNone in Hlookup.
  destruct Hlookup as [[i'| i'] Hfind];
  assert (Heq : i = i') by
      (apply find_true in Hfind;
       apply beq_nat_eq; auto);
  subst...
Qed.

(*
==============
Configuration
==============
*)

Lemma heapLookup_nil :
  forall l,
    heapLookup nil l = None.
Proof with auto.
  intros. destruct l...
Qed.

Lemma heapLookup_not_none :
  forall H l,
    heapLookup H l <> None <->
    exists c F RL, heapLookup H l = Some (c, F, RL).
Proof with eauto.
  intros.
  destruct (heapLookup H l) as [[]|]; crush...
Qed.

Lemma heapLookup_lt :
  forall H l,
    l < length H <->
    exists c F RL, heapLookup H l = Some (c, F, RL).
Proof with auto with arith.
  intros H. induction H as [|[[c F] RL] H']; intros.
  + rewrite heapLookup_nil; crush.
  + split.
    - destruct l; simpl.
      * repeat eexists...
      * introv Hlt. apply Lt.lt_S_n in Hlt. apply IHH'...
    - destruct l; simpl...
      intros Hex. apply IHH' in Hex...
Qed.

Lemma heapLookup_ge :
  forall H l,
    l >= length H <->
    heapLookup H l = None.
Proof with auto using heapLookup_nil with arith.
  split.
  + gen l.
    induction H; destruct l; crush.
  + gen l.
    induction H; introv Hlookup; destruct l; crush.
    apply IHlist in Hlookup...
Qed.

Lemma heapLookup_snoc :
  forall H l obj,
    l < length H ->
    heapLookup H l = heapLookup (snoc H obj) l.
Proof with auto with arith.
  intros H. induction H; introv Hlt.
  + inv Hlt.
  + simpl. destruct l; crush.
Qed.

Lemma heapLookup_in :
  forall H l c f,
    heapLookup H l = Some (c, f) ->
    List.In (c, f) H.
Proof with auto.
  intros H.
  induction H; introv Hlookup.
  + destruct l; inv Hlookup.
  + destruct l as [| l']; simpls.
    - inv Hlookup...
    - right. apply IHlist with l'...
Qed.

Lemma heapExtend_lookup_len :
  forall H obj,
    heapLookup (heapExtend H obj) (length H) = Some obj.
Proof with auto.
  intros H. induction H; crush.
Qed.

Lemma heapExtend_lookup_nlen :
  forall H obj l,
    l <> length H ->
    heapLookup (heapExtend H obj) l = heapLookup H l.
Proof with auto using heapLookup_nil.
  intros H. unfold heapExtend.
  induction H; introv Hneq; simpls; destruct l; crush...
Qed.

Lemma heapUpdate_nil :
  forall l obj,
    heapUpdate nil l obj = nil.
Proof.
  auto.
Qed.

Lemma heapUpdate_length :
  forall H l obj,
    length (heapUpdate H l obj) = length H.
Proof with auto.
  intros. gen l.
  induction H; destruct l; crush.
Qed.

Lemma lookup_heapUpdate_eq :
  forall H l obj,
    l < length H ->
    heapLookup (heapUpdate H l obj) l = Some obj.
Proof with auto.
  introv Hlt. unfolds. gen l.
  induction H as [|obj' H']; intros.
  + inv Hlt.
  + destruct l; crush.
Qed.

Lemma lookup_heapUpdate_neq :
  forall H l1 l2 obj,
    l1 <> l2 ->
    heapLookup (heapUpdate H l2 obj) l1 = heapLookup H l1.
Proof with auto using heapUpdate_nil.
  unfold heapLookup. intros H l1. gen H.
  induction l1 as [|l1']; introv Hneq.
  + destruct H as [|obj' H']...
    destruct l2... contradict Hneq...
  + destruct H as [|obj' H'];
    destruct l2; crush.
Qed.

Lemma heapUpdate_in :
  forall c c' F F' H l,
    In (c, F) (heapUpdate H l (c', F')) ->
    In (c, F) H \/ (c, F) = (c', F').
Proof with auto using in_cons, in_eq.
  introv HIn. gen l. induction H; intros.
  + inv HIn.
  + simpls. destruct l.
    - inv HIn...
    - inv HIn as [|HIn']...
      apply IHlist in HIn'.
      inv HIn'...
Qed.

Lemma declsToFields_null :
  let f_eq f fld := match fld with
                     | Field f' _ _ => beq_nat f f'
                   end
  in
  forall fs f t r,
    find (f_eq f) fs = Some (Field f t r) ->
    (declsToFields fs) f = Some VNull.
Proof with auto.
  introv Hfind. induction fs as [|[f' t']].
  + inv Hfind.
  + simpls. case_extend.
    apply IHfs.
    assert (Hfalse : beq_nat f f' = false) by
        (rewrite EqNat.beq_nat_false_iff; auto).
    rewrite Hfalse in Hfind...
Qed.