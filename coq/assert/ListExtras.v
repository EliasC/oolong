Require Export List.

Require Import CpdtTactics.
Require Import LibTactics.

(*
==================
Lemmas about find
==================
*)

Lemma find_notNone : 
  forall A f l,
    find f l <> None <-> 
    exists (e : A), find f l = Some e.
Proof with eauto.
  induction l.
  + crush.
  + simpl. cases_if...
    split... congruence. 
Qed.

Lemma find_in : 
  forall A f l (x : A), 
    find f l = Some x -> 
    In x l.
Proof with auto.
  induction l as [| h t]; crush.
  cases_if; crush.
Qed.

Lemma find_true : 
  forall A f l (x : A), 
    find f l = Some x -> 
    f x = true.
Proof with auto.
  introv Hfind. induction l.
  + inversion Hfind.
  + simpls. cases_if; crush.
Qed.

Lemma find_app : 
  forall A f l1 l2 (x : A), 
    find f l1 = Some x -> 
    find f (l1 ++ l2) = Some x.
Proof with auto.
  introv Hfind. induction l1; simpl.
  + inversion Hfind.
  + simpls. cases_if; crush.
Qed.

Lemma find_app2 : 
  forall A f l1 l2 (x : A), 
    find f l2 = Some x -> 
    find f l1 = None ->
    find f (l1 ++ l2) = Some x.
Proof with auto.
  induction l1; simpls...
  cases_if; crush. 
Qed.

(*
==================
Lemmas about snoc
==================
*)

Fixpoint snoc {A:Type} (l : list A) (x : A):=
  match l with
    | nil => x :: nil
    | head :: tail => cons head (snoc tail x)
  end. 

Lemma snoc_length :
  forall A l (x : A),
    length (snoc l x) = S (length l).
Proof.
  induction l; crush. 
Qed. 

Lemma snoc_in :
  forall A l (x : A),
    List.In x (snoc l x).
Proof with auto.
  induction l; crush. 
Qed.

Lemma in_snoc :
  forall A l (x y : A),
    List.In x (snoc l y) <->
    List.In x l \/ x = y.
Proof.
  intros. induction l; crush. 
Qed.

(*
====================
Lemmas about remove
====================
*)

Lemma remove_app :
  forall A l1 l2 (x:A) eq_dec,
    remove eq_dec x (l1 ++ l2) =
    remove eq_dec x l1 ++ remove eq_dec x l2.
Proof with auto.
  induction l1; simpls... intros.
  cases_if; crush. 
Qed.

Hint Rewrite remove_app : remove.

Lemma remove_idempotence :
  forall A l (x:A) eq_dec,
    remove eq_dec x (remove eq_dec x l) =
    remove eq_dec x l.
Proof with auto.
  induction l; simpls; intros...
  repeat (elim eq_dec; simpl); crush. 
Qed.

Hint Rewrite remove_idempotence : remove.

Lemma remove_commutative :
  forall A l (x y:A) eq_dec,
    remove eq_dec x (remove eq_dec y l) =
    remove eq_dec y (remove eq_dec x l).
Proof with auto.
  induction l; simpl; intros...
  repeat (elim eq_dec; simpl); crush. 
Qed.

Hint Rewrite remove_commutative : remove.

Lemma remove_in :
  forall A l (x y : A) eq_dec,
    In x (remove eq_dec y l) ->
    In x l.
Proof with eauto.
  induction l; simpl; intros...
  cases_if; crush...
Qed.

Lemma remove_not_in :
  forall A l (x y : A) eq_dec,
    ~ In x l ->
    ~ In x (remove eq_dec y l).
Proof with eauto.
  induction l; simpl; intros...
  cases_if; crush...
Qed.

Hint Constructors NoDup.

Lemma remove_NoDup :
  forall A l (x : A) eq_dec,
  NoDup l -> 
  NoDup (remove eq_dec x l).
Proof with eauto using remove_not_in.
  induction l; simpl; introv Hdup...
  inverts Hdup.
  cases_if... 
Qed.

Lemma remove_in_eq :
  forall A l (x : A) eq_dec,
    ~In x (remove eq_dec x l).
Proof with eauto.
  introv.
  induction l...
  simpl. cases_if; crush.
Qed.

Lemma remove_in_neq :
  forall A l (x y : A) eq_dec,
    In x l ->
    x <> y ->
    In x (remove eq_dec y l).
Proof with eauto.
  introv HIn Hneq.
  induction l...
  simpl. cases_if; crush.
Qed.

(*
==================
Lemmas about app
==================
*)

Lemma Forall_app :
  forall A P l1 l2, 
    @Forall A P l1 -> 
    Forall P l2 -> 
    Forall P (l1 ++ l2).
Proof with auto.
  induction l1...
  introv Hforall.
  inversion Hforall. 
  constructor...
Qed.

Lemma app_eq_nil : 
  forall A l1 l2,
    l1 ++ l2 = nil <-> l1 = nil /\ l2 = @nil A.
Proof with auto using app_eq_nil.
  introv. split... crush.
Qed.

Corollary app_eq_nil_trivial :
  forall A l1 l2,
    l1 = @nil A ->
    l2 = @nil A ->
    l1 ++ l2 = @nil A.
Proof with auto.
  introv Hnil1 Hnil2. apply app_eq_nil...
Qed.

Hint Immediate app_eq_nil_trivial.

Lemma not_in_app :
  forall A l1 l2 (x : A),
    ~ In x (l1 ++ l2) <->
    (~ In x l1) /\ (~ In x l2).
Proof with eauto using in_or_app, in_cons, in_eq.
  intros A l1 l2 x.
  split.
  + introv Hin.
    induction l1...
    simpl in Hin.
    simpl.
    split.
    - intros contra.
      apply Hin. inversion contra...
    - intros contra...
  + introv HIn.
    inverts HIn as HIn1 HIn2.
    induction l1; simpl...
    intros contra.
    inversion contra.    
    - apply HIn1. subst... 
    - apply IHl1...
Qed. 

Hint Constructors NoDup.

Lemma NoDup_app :
  forall A (l1 l2 : list A),
    NoDup (l1 ++ l2) ->
    NoDup l1 /\ NoDup l2.
Proof with eauto.
  introv Hdup.
  induction l1.
  + inversion Hdup...
  + inversion Hdup as [|? ? Hin Hdup'].
    apply IHl1 in Hdup' as (Hdup1 & Hdup2).
    split...
    econstructor...
    apply not_in_app in Hin as []...
Qed.

(*
===================
Lemmas about filter
===================
*)

Lemma filter_in :
  forall A (x : A) p l,
  (forall x y, p x y = true <-> x = y) -> 
  (In x l <-> In x (filter (p x) l)).
Proof with eauto.
  introv Hp.
  split.
  + introv HIn. induction l; 
    simpl; try(cases_if); crush.
    assert (Heq: x = x)...
    apply Hp in Heq. congruence.
  + introv HIn. induction l;
    simpls; try(cases_if); crush. 
Qed.

Lemma filter_not_in :
  forall A (x : A) p l,
  (forall x y, p x y = true <-> x = y) -> 
  (~In x l <-> (filter (p x) l) = nil).
Proof with eauto.    
  introv Hp.
  split.
  + introv HnIn.
    induction l...
    simpl. cases_if; crush.
    apply Hp in H. false.
  + introv Hneq.
    induction l...
    simpls. cases_if; try(congruence). 
    intros contra. inverts contra.
    - assert(p x x = true) by (apply Hp; eauto). 
      congruence.
    - apply IHl...
Qed.

Lemma filter_length :
  forall A (l : list A) p,
    length (filter p l) <= length l.
Proof with eauto.
  introv.
  induction l...
  simpl. cases_if; crush.
Qed. 

Lemma filter_app :
  forall A (l1 l2 : list A) p,
    filter p (l1 ++ l2) = (filter p l1) ++ (filter p l2).
Proof with eauto.
  introv.
  induction l1...
  simpl. cases_if; crush.  
Qed. 

(*
================
Lemmas about in
================
*)

Lemma in_comm :
  forall A l1 l2 (x : A),
    In x (l1 ++ l2) ->
    In x (l2 ++ l1).
Proof with eauto using in_or_app.
  introv HIn.
  apply in_app_or in HIn as []...
Qed.
