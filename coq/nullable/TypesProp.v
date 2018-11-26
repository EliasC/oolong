Require Export Types.
Require Import SyntaxProp.
Require Import WellFormedness.

Ltac simpl_extend_hyp :=
  match goal with
    | H : context[extend _ ?X _ ?X] |- _ =>
      rewrite extend_eq in H

    | H : context[extend _ (env_var (SV ?X)) _ (env_var (SV ?Y))], _ : ?X <> ?Y |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_var (SV _)) _ (env_var (DV _))] |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_var (SV _)) _ (env_loc _)] |- _ =>
      rewrite extend_neq in H

    | H : context[extend _ (env_var (DV ?X)) _ (env_var (DV ?Y))], _ : ?X <> ?Y |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_var (DV _)) _ (env_var (SV _))] |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_var (DV _)) _ (env_loc _)] |- _ =>
      rewrite extend_neq in H

    | H : context[extend _ (env_loc ?X) _ (env_loc ?Y)], _ : ?X <> ?Y |- _ =>
      rewrite extend_neq in H
    | H : context[extend _ (env_loc _) _ (env_var _)] |- _ =>
      rewrite extend_neq in H

    | _ : _ |- _ => fail "No matching hypothesis found"
  end; try congruence.

Hint Extern 1 => simpl_extend_hyp : env.
Hint Extern 1 => case_extend : env.

Ltac trivial_neq :=
  match goal with
    | [_ : _|- env_loc _ <> env_var _] => congruence
    | [H : ?l1 <> ?l2 |- env_loc ?l1 <> env_loc ?l2] => congruence
    | [H : ?l2 <> ?l1 |- env_loc ?l1 <> env_loc ?l2] => congruence
    | [_ : _|- env_var _ <> env_loc _] => congruence
    | [_ : _|- env_var (SV _) <> env_var (DV _)] => congruence
    | [H : ?x <> ?y |- env_var (SV ?x) <> env_var (SV ?y)] => congruence
    | [H : ?y <> ?x |- env_var (SV ?x) <> env_var (SV ?y)] => congruence
    | [_ : _|- env_var (DV _) <> env_var (SV _)] => congruence
    | [H : ?x <> ?y |- env_var (DV ?x) <> env_var (DV ?y)] => congruence
    | [H : ?y <> ?x |- env_var (DV ?x) <> env_var (DV ?y)] => congruence
    | _ => fail 1 "Not a trivial inequality of environment domain variables"
  end.

Hint Extern 1 => trivial_neq : env.

Lemma fields_wfFieldDecl :
  forall P t' t fs,
    wfProgram P t' ->
    fields P t = Some fs ->
    Forall (wfFieldDecl P) fs.
Proof with auto.
  introv wfP Hfields.
  inv wfP.
  destruct t; try(solve[inv Hfields]).
  + unfold fields in Hfields.
    remember (classLookup (cds, ids, e) c) as cLookup.
    symmetry in HeqcLookup.
    destruct cLookup as [[c' i fs' ms] |]...
    inv_eq.
    solve by lookup_forall.
Qed.

Corollary fieldLookup_wfType :
  forall P t' t'' fs f t,
    wfProgram P t' ->
    fields P t'' = Some fs ->
    fieldLookup fs f = Some (Field f t) ->
    wfType P t.
Proof with eauto.
  introv wfP Hfields fLookup.
  eapply fields_wfFieldDecl in Hfields...
  solve by lookup_forall...
Qed.


Lemma extractSigs_wfMethodSigs :
  forall P c mtds,
    Forall (wfMethodDecl P c) mtds ->
    Forall (wfMethodSig P) (extractSigs mtds).
Proof with eauto.
  introv wfMtds.
  induction mtds as [|[m [x t] t' e]]; simpl...
  inv wfMtds as [|? ? wfMtd wfMtds']. constructor...
  inv wfMtd. constructor; crush.
Qed.

Lemma methodSigs_wfMethodSig :
  forall P t' t msigs,
    wfProgram P t' ->
    methodSigs P t msigs ->
    Forall (wfMethodSig P) msigs.
Proof with eauto using extractSigs_wfMethodSigs, Forall_app.
  introv [? ? ? ? wfCds wfIds wfExpr] Hsigs.
  induction Hsigs; try(lookup_forall as wfD; inv wfD)...
Qed.

Corollary methodSigLookup_wfType :
  forall P t' t msigs m x t1 t2,
    wfProgram P t' ->
    methodSigs P t msigs ->
    methodSigLookup msigs m = Some (MethodSig m (x, t1) t2) ->
    wfType P t2.
Proof with eauto using methodSigs_wfMethodSig.
  introv wfP Hsigs Hsig.
  eapply methodSigs_wfMethodSig in Hsigs...
  lookup_forall as wfMsig.
  inv wfMsig...
Qed.

(*
========================
Well-formed environment
========================
*)

Hint Constructors wfProgram.
Hint Constructors wfEnv.
Hint Constructors wfType.

(*
Lemma wfEnv_empty :
  forall P,
    wfEnv P empty.
Proof with auto.
  constructor; introv H; inv H.
Qed.
*)

Lemma wfEnv_equiv :
  forall P Gamma Gamma',
    (forall x, Gamma x = Gamma' x) ->
    wfEnv P Gamma ->
    wfEnv P Gamma'.
Proof with eauto.
  introv Hequiv wfGamma.
  constructor; introv;
  rewrite <- Hequiv; inv wfGamma...
Qed.

Hint Immediate wfEnv_equiv : env.

Lemma wfEnv_extend_var :
  forall P Gamma x t,
    wfEnv P Gamma ->
    wfType P t ->
    wfEnv P (extend Gamma (env_var x) t).
Proof with eauto.
  constructor; intros x' t'; case_extend; inv H...
Qed.

Hint Resolve wfEnv_extend_var : env.

Lemma wfEnv_extend_loc :
  forall P Gamma l t,
    wfEnv P Gamma ->
    wfType P t ->
    (exists c n, t = TClass c n) ->
    wfEnv P (extend Gamma (env_loc l) t).
Proof with eauto.
  constructor; intros x' t'; case_extend; inv H; crush...
Qed.

Hint Resolve wfEnv_extend_loc : env.

Lemma wfEnv_drop :
  forall P Gamma x,
    wfEnv P Gamma ->
    wfEnv P (drop Gamma x).
Proof with eauto with env.
  introv wfGamma.
  inv wfGamma.
  econstructor.
  + introv Henv.
    unfold drop in Henv.
    cases_if...
  + introv Henv.
    unfold drop in Henv.
    cases_if...
Qed.

Hint Resolve wfEnv_drop : env.

Lemma wfEnv_subst :
  forall P Gamma x y t,
    wfEnv P Gamma ->
    wfEnv P (extend Gamma (env_var x) t) ->
    wfEnv P (extend Gamma (env_var y) t).
Proof with eauto with env.
  introv wfGamma wfGamma'.
  inv wfGamma'...
Qed.

Hint Resolve wfEnv_subst : env.

(*
============
Subsumption
============
*)

Hint Constructors wfSubsumption.

Lemma wfSubsumption_refl :
  forall Gamma,
    wfSubsumption Gamma Gamma.
Proof with eauto.
  auto.
Qed.

Hint Immediate wfSubsumption_refl.

Lemma wfSubsumption_equiv :
  forall Gamma Gamma',
    (forall x, Gamma x = Gamma' x) ->
    wfSubsumption Gamma Gamma'.
Proof with eauto.
  constructors;
  crush.
Qed.

Hint Immediate wfSubsumption_equiv.

Lemma wfSubsumption_trans :
  forall Gamma1 Gamma2 Gamma3,
    wfSubsumption Gamma1 Gamma2 ->
    wfSubsumption Gamma2 Gamma3 ->
    wfSubsumption Gamma1 Gamma3.
Proof with eauto.
  constructors; crush.
  inv H. inv H0. crush.
Qed.

Lemma wfSubsumption_extend :
  forall Gamma Gamma' x t,
    wfSubsumption Gamma Gamma' ->
    wfSubsumption (extend Gamma x t) (extend Gamma' x t).
Proof with eauto with env.
  introv wfSub.
  inv wfSub...
Qed.

Lemma wfSubsumption_fresh :
  forall Gamma Gamma' x t,
    wfSubsumption Gamma Gamma' ->
    fresh Gamma x ->
    wfSubsumption Gamma (extend Gamma' x t).
Proof with eauto with env.
  introv wfSub Hfresh.
  inv wfSub...
Qed.

Hint Immediate wfSubsumption_fresh.

Lemma wfSubsumption_empty :
  forall Gamma,
    wfSubsumption empty Gamma.
Proof with eauto with env.
  constructor...
  introv contra.
  inv contra.
Qed.

Hint Immediate wfSubsumption_empty.

Lemma wfSubsumption_frame :
  forall Gamma Gamma1 Gamma2,
    wfFrame Gamma Gamma1 Gamma2 ->
    wfSubsumption Gamma1 Gamma /\
    wfSubsumption Gamma2 Gamma.
Proof with eauto with env.
  introv frameRule.
  inv frameRule...
Qed.

(*
==========
Subtyping
==========
*)

Lemma nullable_wfType :
  forall P t,
    wfType P t ->
    wfType P (nullable t).
Proof with eauto.
  introv wfT. induction wfT; unfolds nullable...
Qed.

Hint Immediate nullable_wfType.

Lemma subtypeOf_class :
  forall P t c n,
    subtypeOf P t (TClass c n) ->
    exists n', t = TClass c n'.
Proof with eauto.
  introv Hsub. remember (TClass c n) as t2.
  gen c. gen n.
  induction Hsub; intros; try(inv Heqt2)...
  - apply IHHsub2 in Heqt2 as Heq... subst. inv Heq. eapply IHHsub1...
  - destruct t2; simpls; try congruence. inv_eq.
    lets IH: IHHsub ___ c...
    inv IH... unfolds nullable...
  - destruct t2; simpls; try congruence. inv_eq.
    lets IH: IHHsub ___ c...
Qed.

Hint Immediate subtypeOf_class.

Lemma subtypeOf_wfType :
  forall P t' t1 t2,
    wfProgram P t' ->
    subtypeOf P t1 t2 ->
    wfType P t1 /\ wfType P t2.
Proof with eauto.
  introv [? ? ? ? wfCs wfIs ?] Hsub.
  subtypeOf_cases(induction Hsub) Case;
    split;
    try(constructor; lookup_forall as wfD; inv wfD); crush;
    match goal with
      | [H: methodSigs _ _ _ |- _] =>
        solve[inv H; crush]
      | [H1: methodSigs _ _ _, H2: methodSigs _ _ _ |- _] =>
        solve[inv H1; crush
             |inv H2; crush]
    end.
Qed.

Corollary subtypeOf_wfTypeSub :
  forall P t' t1 t2,
    wfProgram P t' ->
    subtypeOf P t1 t2 ->
    wfType P t1.
Proof with eauto.
  introv wfP Hsub...
  eapply subtypeOf_wfType in Hsub; crush...
Qed.

Hint Immediate subtypeOf_wfTypeSub.

Corollary subtypeOf_wfTypeSup :
  forall P t' t1 t2,
    wfProgram P t' ->
    subtypeOf P t1 t2 ->
    wfType P t2.
Proof with eauto.
  introv wfP Hsub...
  eapply subtypeOf_wfType in Hsub; crush...
Qed.

Hint Immediate subtypeOf_wfTypeSup.

Lemma nullable_isNullable :
  forall t,
    isNullable (nullable t).
Proof with eauto.
  introv. destruct t; crush.
Qed.

Lemma subtypeOf_isNullable :
  forall P t1 t2,
    subtypeOf P t1 t2 ->
    isNullable t1 ->
    isNullable t2.
Proof with eauto using nullable_isNullable.
  introv Hsub Hnull.
  induction Hsub; inv Hnull...
Qed.

(*
========
hasType
========
*)

Hint Constructors hasType.

Lemma hasType_wfType :
  forall P Gamma e t' t,
    wfProgram P t' ->
    P; Gamma |- e \in t ->
    wfType P t.
Proof with eauto using subtypeOf_wfTypeSup, methodSigLookup_wfType, fieldLookup_wfType.
  intros P Gamma e. gen Gamma.
  expr_cases (induction e) Case;
    introv wfP hasType; inv hasType;
    match goal with
      | [H: wfEnv _ ?Gamma |- _] =>
        inv H
      | _ => idtac
    end...
Qed.

Hint Resolve hasType_wfType : env.

Lemma hasType_subsumption :
  forall e P t' Gamma Gamma' t,
    wfProgram P t' ->
    wfSubsumption Gamma Gamma' ->
    wfEnv P Gamma' ->
    P; Gamma |- e \in t ->
    P; Gamma' |- e \in t.
Proof with eauto using wfSubsumption_extend with env.
  expr_cases (induction e) Case;
    introv [? ? ? ? wfCds wfIds wfExpr] [Hsub] wfGamma hasType; inv hasType;
  try(
      solve[
          repeat
          match goal with
            | [H: hasType _ _ (EVar ?v) _ |- _] => inv H
            | [H: hasType _ _ (EVal ?v) _ |- _] => inv H
          end;
          constructors; eauto;
          constructors; try(rewrite Heq);
          eauto using wfSubsumption_extend with env
        ]
    )...
  + constructors...
    eapply IHe2 with
    (Gamma := extend Gamma (env_var _) t1)...
  + constructors...
    inv H2.
    constructors...
Qed.

Hint Immediate hasType_subsumption : env.

Lemma hasType_wfEnv :
  forall P t' Gamma e t,
    wfProgram P t' ->
    P; Gamma |- e \in t ->
    wfEnv P Gamma.
Proof with eauto.
  induction e; introv wfP hasType; inv hasType;
  try(eapply IHe1); try(eapply IHe); try(eassumption).
  match goal with H: hasType _ _ (EVar ?v) _ |- _ => inv H end...
  apply wfSubsumption_frame in H2 as [Hsub1].
  eapply hasType_subsumption with (Gamma := Gamma1)...
Qed.

Hint Immediate hasType_wfEnv : env.

Corollary hasType_subsumption_extend :
  forall P t' Gamma Gamma' e x t1 t,
    wfProgram P t' ->
    wfSubsumption Gamma Gamma' ->
    wfEnv P Gamma ->
    wfEnv P Gamma' ->
    P; extend Gamma (env_var x) t1 |- e \in t ->
    P; extend Gamma' (env_var x) t1 |- e \in t.
Proof with eauto using wfSubsumption_extend with env.
  introv wfP wfSub wfGamma wfGamma' hasType.
  assert (wfT: wfType P t1)...
  eapply hasType_subsumption
  with (Gamma := extend Gamma (env_var x) t1)...
Qed.

Corollary hasType_flip :
  forall P t' Gamma x y e t t1 t2,
    wfProgram P t' ->
    P; (extend (extend Gamma x t1) y t2) |- e \in t ->
    x <> y ->
    P; (extend (extend Gamma y t2) x t1) |- e \in t.
Proof with eauto using hasType_subsumption.
  introv wfP hasType Hneq.
  eapply hasType_subsumption
  with (Gamma := (extend (extend Gamma x t1) y t2))...
  + econstructor.
    introv.
    rewrite extend_order...
  + eapply hasType_wfEnv in hasType...
    apply wfEnv_equiv
    with (extend (extend Gamma x t1) y t2)...
Qed.

Corollary hasType_shadow :
  forall P t' Gamma x y e t t1 t2,
    wfProgram P t' ->
    P; (extend (extend Gamma x t1) y t2) |- e \in t ->
    x = y ->
    P; (extend Gamma y t2) |- e \in t.
Proof with eauto with env.
  introv wfP hasType Hneq.
  eapply hasType_subsumption
  with (Gamma' := extend Gamma y t2)
  in hasType; eauto 2 with env.
  eapply hasType_wfEnv in hasType; eauto.
  apply wfEnv_equiv
  with (extend (extend Gamma x t1) y t2)...
Qed.

Lemma hasType_extend_loc :
  forall e P Gamma t t' l c n,
    wfProgram P t' ->
    P; Gamma |- e \in t ->
    Gamma (env_loc l) = None ->
    wfType P (TClass c n) ->
    P; extend Gamma (env_loc l) (TClass c n) |- e \in t.
Proof with eauto 4 using hasType, hasType_flip with env.
  expr_cases(induction e) Case;
    introv wfP hasType Heq wfT; inv hasType;
  try(econstructor; try(case_extend)); eauto 3;
  match goal with
    | [H: _; _ |- EVar _ \in _ |- _] => inv H; constructor
    | [H: _; _ |- EVal _ \in _ |- _] => inv H; econstructor
    | _ => idtac
  end...
  + Case "EPar".
    inverts H2 as frame1 frame2 disj1 disj2...
    econstructor; introv envLookup...
    - case_extend...
      apply frame1 in envLookup. rewrite_and_invert.
    - case_extend...
      apply frame2 in envLookup. rewrite_and_invert.
Qed.

Lemma hasType_subst_fresh :
  forall P Gamma e t x y,
    P; Gamma |- e \in t ->
    fresh Gamma (env_var (SV x)) ->
    P; Gamma |- subst x y e \in t.
Proof with eauto using no_locks_subst.
  introv hasType Hfresh.
  gen Gamma. gen t.
  expr_cases (induction e) Case;
    introv hasType Hfresh;
    inv hasType;
    try(econstructor); try(unfold subst_var);
    try(destruct_var); try(cases_if);
    try(solve[
          match goal with
          | [hasType: _; _ |- EVar _ \in _ |- _] => inv hasType
          end; congruence])...
  + Case "ELet".
    apply IHe2...
    unfold fresh. rewrite extend_neq...
    congruence.
  + Case "EPar".
    apply IHe1...
    inv H2. unfold fresh.
    remember (Gamma1 (env_var (SV x))) as G1.
    symmetry in HeqG1. destruct G1... apply H in HeqG1...
    congruence.
  + Case "EPar".
    apply IHe2...
    inv H2. unfold fresh.
    remember (Gamma2 (env_var (SV x))) as G2.
    symmetry in HeqG2. destruct G2... apply H0 in HeqG2...
    congruence.
Qed.

Lemma hasType_subst :
  forall P Gamma e t t' t'' x y,
    wfProgram P t'' ->
    wfEnv P Gamma ->
    P; extend Gamma (env_var (SV x)) t' |- e \in t ->
    fresh Gamma (env_var (DV y)) ->
    P; extend Gamma (env_var (DV y)) t' |- subst x y e \in t.
Proof with eauto using no_locks_subst with env.
  introv wfP wfGamma hasType Hfresh.
  gen Gamma.
  gen t. gen t'.
  gen x. gen y.
  expr_cases (induction e) Case;
    intros; simpl; try(unfold subst_var); inv hasType;
    repeat
    match goal with
      | [x : var, H : hasType _ _ (EVar ?x) _ |- _] => inv H
      | [H : hasType _ _ (EVal _) _ |- _] => inv H
      | _ => idtac
    end; repeat(destruct_var); try(cases_if); subst;
    try(simpl_extend_hyp);
    try(solve[try(econstructor);
               try(case_extend);
               try(inv_eq); eauto using no_locks_subst with env]).
    + Case "ELet".
      econstructor...
      eapply hasType_shadow in H4; eauto 3 with env.
      eapply hasType_subsumption
      with (Gamma := extend Gamma (env_var (SV s)) t0);
        eauto 4 with env.
    + Case "ELet".
      econstructor... eapply hasType_flip; eauto 3 with env.
      apply IHe2; eauto 3 with env.
      eapply hasType_flip...
    + Case "EPar".
      remember (Gamma1 (env_var (SV x))) as G1.
      symmetry in HeqG1.
      destruct G1.
      - eapply T_Par
        with (Gamma1 := extend (drop Gamma1 (env_var (SV x))) (env_var (DV y)) t')
             (Gamma2 := drop Gamma2 (env_var (SV x)))...
        * {econstructor.
           + introv Henv. case_extend...
             rewrite extend_neq in Henv...
             inv H2.
             unfold drop in Henv. cases_if...
             apply H in Henv. rewrite extend_neq in Henv...
           + introv Henv. unfold drop in Henv. cases_if...
             inv H2. apply H1 in Henv.
             rewrite extend_neq in Henv...
           + introv Henv.
             destruct (id_eq_dec (env_var (DV y)) (env_var x0)).
             - inv_eq. simpl_extend_hyp. inv_eq.
               case_drop...
               remember (Gamma2 (env_var (DV y))) as G2.
               symmetry in HeqG2. destruct G2...
               inv H2. apply H1 in HeqG2.
               rewrite extend_neq in HeqG2...
               congruence.
             - rewrite extend_neq in Henv...
               case_drop...
               unfold drop in Henv.
               cases_if... inv H2. apply H10 in Henv...
           + introv Henv. case_extend...
             - inv_eq. unfold drop in Henv. cases_if...
               inv H2. apply H1 in Henv...
             - case_drop...
               unfold drop in Henv. cases_if...
               inv H2. apply H11 in Henv...
          }
        * {apply IHe1...
           + eapply hasType_subsumption
             with (Gamma := Gamma1); eauto 3 with env.
             econstructor...
             introv Henv. case_extend. rewrite_and_invert.
             inv H2. apply H in HeqG1...
             case_drop...
             apply wfEnv_extend_var...
           + unfold fresh.
             remember (Gamma1 (env_var (DV y))) as G1'.
             symmetry in HeqG1'. destruct G1'... inv H2.
             apply H in HeqG1'. rewrite extend_neq in HeqG1'...
             congruence.
             case_drop...
          }
        * apply hasType_subst_fresh... inv H2.
          apply H1 in HeqG1...
          eapply hasType_subsumption with (Gamma := Gamma2)...
          econstructor... introv Henv. case_drop...
          unfold fresh. case_drop...
      - remember (Gamma2 (env_var (SV x))) as G2.
        symmetry in HeqG2.
        destruct G2.
        * {eapply T_Par
           with (Gamma1 := drop Gamma1 (env_var (SV x)))
                (Gamma2 := extend (drop Gamma2 (env_var (SV x))) (env_var (DV y)) t')...
           + econstructor.
             - introv Henv. unfold drop in Henv. cases_if...
               inv H2. apply H0 in Henv.
               rewrite extend_neq in Henv...
             - introv Henv. case_extend...
               rewrite extend_neq in Henv...
               inv H2. unfold drop in Henv. cases_if...
               apply H0 in Henv. rewrite extend_neq in Henv...
             - introv Henv. unfold drop in Henv.
               cases_if... case_extend...
               * inv_eq. inv H2. apply H0 in Henv...
               * case_drop...
                 inv H2...
             - introv Henv.
               destruct (id_eq_dec (env_var (DV y)) (env_var x0)).
               * inv_eq. simpl_extend_hyp. inv_eq.
                 case_drop...
                 remember (Gamma1 (env_var (DV y))) as G1'.
                 symmetry in HeqG1'. destruct G1'...
                 inv H2. apply H0 in HeqG1'.
                 rewrite extend_neq in HeqG1'...
                 congruence.
               * rewrite extend_neq in Henv...
                 case_drop...
                 unfold drop in Henv.
                 cases_if... inv H2. apply H11 in Henv...
           + apply hasType_subst_fresh... inv H2.
             apply H7 in HeqG2...
             eapply hasType_subsumption
             with (Gamma := Gamma1)...
             econstructor... introv Henv. case_drop...
             unfold fresh. case_drop...
           + apply IHe2...
             - eapply hasType_subsumption
               with (Gamma := Gamma2); eauto 3 with env.
               econstructor...
               introv Henv. case_extend. rewrite_and_invert.
               inv H2. apply H0 in HeqG2...
               case_drop...
               apply wfEnv_extend_var...
             - unfold fresh.
               remember (Gamma2 (env_var (DV y))) as G2'.
               symmetry in HeqG2'. destruct G2'... inv H2.
               apply H0 in HeqG2'. rewrite extend_neq in HeqG2'...
               congruence.
               case_drop...
          }
        * {eapply T_Par
           with (Gamma1 := Gamma1) (Gamma2 := Gamma2)...
           + econstructor...
             - introv Henv. case_extend.
               inv H2. apply H in Henv...
               inv H2. destruct (id_eq_dec x0 (env_var (SV x))).
               * subst. congruence.
               * apply H in Henv...
                 rewrite extend_neq in Henv...
             - introv Henv. case_extend.
               inv H2. apply H0 in Henv...
               inv H2. destruct (id_eq_dec x0 (env_var (SV x))).
               * subst. congruence.
               * apply H0 in Henv...
                 rewrite extend_neq in Henv...
             - inv H2...
             - inv H2...
           + apply hasType_subst_fresh...
           + apply hasType_subst_fresh...
          }
Qed.

(*
============
Corollaries
============
*)

Corollary envModelsVars :
  forall P Gamma V n x t,
    wfVars P Gamma n V ->
    Gamma (env_var (DV x)) = Some t ->
    exists v, V x = Some v /\ P; Gamma |- EVal v \in t.
Proof with eauto.
  introv wfV envLookup.
  inv wfV...
Qed.

Hint Immediate envModelsVars.

Corollary wfVars_fresh :
  forall P Gamma V n m,
    wfVars P Gamma n V ->
    n <= m ->
    fresh V (DVar m).
Proof with eauto.
  introv wfV.
  inverts wfV as _ _ _ Hfresh...
Qed.

Hint Immediate wfVars_fresh.

Corollary wfVars_fresh_env :
  forall P Gamma V n m,
    wfVars P Gamma n V ->
    n <= m ->
    fresh Gamma (env_var (DV (DVar m))).
Proof with eauto.
  introv wfV Hle.
  remember (Gamma (env_var (DV (DVar m)))) as t.
  destruct t...
  symmetry in Heqt.
  eapply envModelsVars in Heqt as (v & vLookup & _)...
  rewrite wfVars_fresh in vLookup...
Qed.

Hint Immediate wfVars_fresh_env.

Corollary envModelsHeap :
  forall P Gamma H l t,
    wfHeap P Gamma H ->
    Gamma (env_loc l) = Some t ->
    exists c n F RL, heapLookup H l = Some (c, F, RL) /\
                wfFields P Gamma c F /\
                t = TClass c n.
Proof with eauto.
  introv wfH envLookup.
  inverts wfH as wfGamma.
  assert (Hclass: exists c n, t = TClass c n)
    by (inv wfGamma; eauto).
  inv Hclass as [c [n]].
  exists c n.
  assert (Hlookup: exists F RL, heapLookup H l = Some (c, F, RL) /\
                                wfFields P Gamma c F)...
  inv Hlookup as [F [RL]].
  exists F RL. crush.
Qed.

Hint Immediate envModelsHeap.

Ltac wfEnvLookup :=
  match goal with
      | [wfV : wfVars ?P ?Gamma ?n ?V,
         envLookup: ?Gamma (env_var (DV ?x)) = Some ?t |- _] =>
        assert (HVex: exists v, V x = Some v /\ P; Gamma |- EVal v \in t)
          by eauto using envModelsVars;
          let v := fresh "v" in
          let Vlookup := fresh "Vlookup" in
          let hasType := fresh "hasType" in
          inv HVex as [v [Vlookup hasType]];
          clear envLookup
    | [wfH : wfHeap ?P ?Gamma ?H,
             envLookup: ?Gamma (env_loc ?l) = Some ?t |- _] =>
      assert (Hex: exists c n F RL,
                     heapLookup H l = Some (c, F, RL) /\
                     wfFields P Gamma c F /\
                     t = TClass c n)
        by eauto using envModelsHeap;
        let c := fresh "c" in
        let n := fresh "n" in
        let F := fresh "F" in
        let RL := fresh "RL" in
        let Hlookup := fresh "Hlookup" in
        let wfF := fresh "wfF" in
        let Heq := fresh "Heq" in
        inv Hex as (c & n & F & RL & Hlookup & wfF & Heq);
          try(inv Heq); clear envLookup
    | _ => fail 1 "no well-formed environment lookup in context"
  end.

Corollary wfHeap_fresh_env :
  forall P Gamma H,
    wfHeap P Gamma H ->
    forall l, length H <= l -> fresh Gamma (env_loc l).
Proof with eauto.
  introv wfH Hle.
  unfold fresh.
  remember (Gamma (env_loc l)) as t.
  symmetry in Heqt.
  destruct t...
  wfEnvLookup.
  assert (contra: l < length H)
    by (apply heapLookup_lt; eauto).
  omega.
Qed.

Hint Immediate wfHeap_fresh_env.

Corollary heapMirrorsEnv :
  forall P Gamma H l c,
    wfHeap P Gamma H ->
    (exists F RL, heapLookup H l = Some (c, F, RL)) ->
    Gamma (env_loc l) = Some (TClass c false).
Proof with eauto.
  introv wfH Hlookup.
  inverts wfH as wfGamma envModels heapMirrors.
  destruct Hlookup as [F [RL Hlookup]].
  assert (Hlookup' : heapLookup H l <> None) by congruence.
  apply heapMirrors in Hlookup' as [c' Hlookup'].
  assert (c = c')
    by (apply envModels in Hlookup' as [F' [RL' [Hlookup']]];
        rewrite_and_invert).
  subst...
Qed.

Hint Immediate heapMirrorsEnv.
