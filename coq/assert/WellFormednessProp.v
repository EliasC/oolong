Require Export WellFormedness.
Require Import SyntaxProp.
Require Import TypesProp.
Require Import Shared.

(*
========================
Field and method lookup
========================
*)


Lemma wfProgram_wfMethodDecl :
  forall P t' c ms m mtd,
    wfProgram P t' ->
    methods P (TClass c) = Some ms ->
    methodLookup ms m = Some mtd ->
    wfMethodDecl P c mtd.
Proof with auto.
  introv wfP Hmethods mLookup.
  inv wfP.
  unfold methods in Hmethods.
  remember (classLookup (cds, ids, e) c) as cLookup.
  symmetry in HeqcLookup.
  destruct cLookup as [[c' i fs ms'] |]...
  inv_eq.
  assert (Heq : c = c') by
      (unfold classLookup in HeqcLookup;
       apply find_true in HeqcLookup;
       apply beq_nat_eq; auto).
  subst.
  lookup_forall as wfCls.
  inv wfCls.
  lookup_forall mtd as wfMtd...
Qed.


Corollary dyn_wfFieldLookup :
  forall P Gamma c F fs f t,
    wfFields P Gamma c F ->
    fields P (TClass c) = Some fs ->
    fieldLookup fs f = Some (Field f t) ->
    exists v, F f = Some v /\ P; Gamma |- (EVal v) \in t.
Proof with eauto.
  introv wfF Hfields fLookup.
  inv wfF. rewrite_and_invert...
Qed.

Hint Immediate dyn_wfFieldLookup.

(*
------------
Method sigs
------------
*)

Hint Constructors methodSigs.

Lemma extractSigs_sound :
  forall mtds m x t t',
    (exists e, methodLookup mtds m = Some (Method m (x, t) t' e)) <->
    methodSigLookup (extractSigs mtds) m = Some (MethodSig m (x, t) t').
Proof with eauto.
  intros. split.
  + gen t t' m x.
    induction mtds as [|[m [x t] t' e]]; simpl;
    introv H; inv H as [e' Hsigs]...
    cases_if... inv_eq.
  + gen t t' m x.
    induction mtds as [|[m [x t] t' e]]; simpl;
    introv mLookup; inv mLookup...
    cases_if; crush...
Qed.

Lemma methodSigs_deterministic :
  forall P t msigs1 msigs2,
    methodSigs P t msigs1 ->
    methodSigs P t msigs2 ->
    msigs1 = msigs2.
Proof with eauto.
  introv Hsigs1 Hsigs2.
  gen msigs2.
  induction Hsigs1; introv Hsigs2;
  inv Hsigs2; try(rewrite_and_invert)...
  rewrite IHHsigs1_1 with msigs3...
  rewrite IHHsigs1_2 with msigs4...
Qed.

Lemma methodSigs_wfType_exists :
  forall P t' t,
    wfProgram P t' ->
    (wfType P t <->
     exists msigs, methodSigs P t msigs).
Proof with eauto.
  introv [? ? ? wfCds wfIds wfExpr].
  split.
  + intros wfT.
    inv wfT as [c cLookup|i iLookup|]...
    - apply classLookup_not_none in cLookup as [i [fs [ms]]]...
    - apply interfaceLookup_not_none in iLookup.
      inv iLookup as [[msigs]|[i1 [i2]]]...
      * intros. lookup_forall as wfId. inv wfId...
  + intros Hex. destruct Hex as [msigs Hsigs].
    destruct t; inv Hsigs; constructor; crush.
Qed.

Lemma methodSigs_sub :
  forall P t t1 t2 m msigs1 msigs2 msig,
    wfProgram P t ->
    subtypeOf P t1 t2 ->
    methodSigs P t1 msigs1 ->
    methodSigs P t2 msigs2 ->
    methodSigLookup msigs2 m = Some msig ->
    methodSigLookup msigs1 m = Some msig.
Proof with eauto using
                 methodSigs_deterministic,
                 methodSigs_wfType_exists,
                 subtypeOf_wfTypeSub,
                 subtypeOf_wfTypeSup.
  introv [? ? ? ? wfCds wfIds wfExpr] Hsub
         Hsigs1 Hsigs2 Hsig.
  gen msigs1 msigs2 msig.
  subtypeOf_cases(induction Hsub) Case; intros.
  + Case "Sub_Class".
    lookup_forall as wfCd. inv wfCd.
    assert (msigs2 = (extractSigs ms))...
    subst. inv Hsigs1; rewrite_and_invert.
  + Case "Sub_InterfaceLeft".
    inv Hsigs1; rewrite_and_invert.
    assert (msigs0 = msigs2)...
    subst. apply find_app...
  + inv Hsigs1; rewrite_and_invert.
    assert (msigs2 = msigs3)...
    subst. apply find_app2...
    lookup_forall as wfId.
    inverts wfId as Hsigs3 Hsigs4 sigsDisjoint1 sigsDisjoint2.
    assert (msigs0 = msigs1)...
    assert (msigs2 = msigs3)...
    subst. fold (methodSigLookup msigs1 m).
    eapply sigsDisjoint2...
  + asserts_rewrite (msigs1 = msigs2)...
  + rename msigs2 into msigs3.
    rename Hsigs2 into Hsigs3.
    assert (wfT1: wfType (cds, ids, e) t1)...
    assert (wfT2: wfType (cds, ids, e) t2)...
    eapply methodSigs_wfType_exists in wfT2 as []...
(*  + inv Hsigs2. inv Hsig.*)
Qed.

(*
==============
Configuration
==============
*)

(*
---------
wfFields
---------
*)

Lemma wfFields_declsToFields :
  forall P t' c i fs ms Gamma,
    wfProgram P t' ->
    wfEnv P Gamma ->
    classLookup P c = Some (Cls c i fs ms) ->
    wfFields P Gamma c (declsToFields fs).
Proof with eauto using
                 fields_wfFieldDecl,
                 declsToFields_null.
  introv wfProgram wfEnv Hlookup.
  assert (fields P (TClass c) = Some fs)
    by (unfolds; rewrite Hlookup; auto).
  assert (Forall (wfFieldDecl P) fs)...
  econstructor...
  intros.
  lookup_forall as wfF. inv wfF...
Qed.

Lemma wfFields_extend :
  forall P Gamma c fs f t F v,
    fields P (TClass c) = Some fs ->
    fieldLookup fs f = Some (Field f t) ->
    wfFields P Gamma c F ->
    P; Gamma |- EVal v \in t ->
    wfFields P Gamma c (extend F f v).
Proof with eauto with env.
  introv Hfields fLookup wfF hasType.
  econstructor...
  introv fLookup'.
  inv wfF.
  case_extend; repeat rewrite_and_invert...
Qed.

Lemma wfFields_envExtend :
  forall P t' Gamma c F l c',
    wfProgram P t' ->
    wfFields P Gamma c F ->
    wfEnv P Gamma ->
    fresh Gamma (env_loc l) ->
    wfType P (TClass c') ->
    wfFields P (extend Gamma (env_loc l) (TClass c')) c F.
Proof with eauto using hasType_extend_loc.
  introv wfP wfF wfGamma Hfresh wfT.
  inverts wfF as Hfields wfFlds.
  econstructor...
  introv Hlookup.
  apply wfFlds in Hlookup as (v & Heq & hasType)...
Qed.

Lemma wfFields_invariance :
  forall P t' c Gamma Gamma' F,
    wfProgram P t' ->
    (forall l, Gamma (env_loc l) = Gamma' (env_loc l)) ->
    wfEnv P Gamma' ->
    wfFields P Gamma c F ->
    wfFields P Gamma' c F.
Proof with eauto using hasType_wfType.
  introv wfP envSub wfGamma' wfF.
  inverts wfF as Hfields wfFld.
  econstructor...
  introv fLookup.
  apply wfFld in fLookup as (v & Ff & hasType).
  exists v. split...
  destruct v...
  + inv hasType.
    econstructor...
    rewrite <- envSub...
Qed.

Lemma wfHeap_wfObject :
  forall P Gamma H l c F L,
    wfHeap P Gamma H ->
    heapLookup H l = Some (c, F, L) ->
    wfFields P Gamma c F.
Proof with eauto.
  introv wfH Hlookup.
  inverts wfH as _ envModelsHeap heapMirrorsEnv.
  assert (Hl: heapLookup H l <> None) by crush.
  apply heapMirrorsEnv in Hl.
  destruct Hl as [c' envLookup].
  apply envModelsHeap in envLookup as (F' & L' & ? & ?).
  rewrite_and_invert.
Qed.

Lemma wfHeap_wfFields :
  forall P Gamma H l c F RL,
    wfHeap P Gamma H ->
    heapLookup H l = Some (c, F, RL) ->
    wfFields P Gamma c F.
Proof with eauto.
  introv wfH Hlookup.
  eapply wfHeap_wfObject in Hlookup as []...
  constructors...
Qed.

(*
-------
wfHeap
-------
*)

Hint Constructors wfHeap.

Lemma wfHeap_fresh :
  forall P Gamma H l,
    wfHeap P Gamma H ->
    heapLookup H l = None ->
    fresh Gamma (env_loc l).
Proof with eauto.
  introv wfH Hlookup.
  inverts wfH as wfGamma envModelsHeap heapMirrorsEnv.
  unfold fresh. remember (Gamma (env_loc l)) as t...
  destruct t...
  symmetry in Heqt.
  assert (tClass: exists c, t = TClass c) by (inv wfGamma; eauto).
  inv tClass as [c''].
  apply envModelsHeap in Heqt.
  inv Heqt as [F' [RL [contra]]]. rewrite_and_invert.
Qed.

Lemma wfHeap_extend :
  forall P t' Gamma H c F L,
    wfProgram P t' ->
    wfHeap P Gamma H ->
    wfType P (TClass c) ->
    wfFields P Gamma c F ->
    wfHeap P (extend Gamma (env_loc (length H)) (TClass c)) (heapExtend H (c, F, L)).
Proof with eauto with env.
  introv wfP wfH wfT wfF.
  inverts wfH as wfGamma envModelsHeap heapMirrorsEnv.
  constructor...
  + introv envLookup.
    destruct (id_eq_dec l (length H)).
    - subst. simpl_extend_hyp. inv_eq.
      rewrite heapExtend_lookup_len.
      eexists; eexists; split...
      eapply wfFields_envExtend...
      eapply wfHeap_fresh...
      apply heapLookup_ge...
    - rewrite extend_neq in envLookup...
      rewrite heapExtend_lookup_nlen...
      apply envModelsHeap in envLookup as (F' & RL' & Hlookup & wfF')...
      eexists; eexists; split...
      eapply wfFields_envExtend...
      eapply wfHeap_fresh...
      apply heapLookup_ge...
  + introv Hlookup.
    destruct (id_eq_dec l (length H))...
    rewrite heapExtend_lookup_nlen in Hlookup...
Qed.

Lemma wfHeap_update :
  forall P Gamma H l c F RL RL' F',
    wfHeap P Gamma H ->
    heapLookup H l = Some (c, F, RL) ->
    wfFields P Gamma c F' ->
    wfHeap P Gamma (heapUpdate H l (c, F', RL')).
Proof with eauto.
  introv wfH Hlookup wfF'.
  inverts wfH as wfGamma envModelsHeap heapMirrorsEnv.
  constructor...
  + introv envLookup.
    destruct (id_eq_dec l l0).
    - subst.
      rewrite lookup_heapUpdate_eq
        by (apply heapLookup_lt; eauto).
      apply envModelsHeap in envLookup as (F'' & RL'' & Hlookup' & wfF'').
      rewrite_and_invert...
    - rewrite lookup_heapUpdate_neq...
  + introv Hlookup'.
    apply heapMirrorsEnv.
    destruct (id_eq_dec l l0).
    - subst.
      rewrite heapLookup_not_none...
    - rewrite lookup_heapUpdate_neq in Hlookup'...
Qed.

Lemma wfHeap_invariance :
  forall P t' Gamma Gamma' H,
    wfProgram P t' ->
    (forall l, Gamma (env_loc l) = Gamma' (env_loc l)) ->
    wfEnv P Gamma' ->
    wfHeap P Gamma H ->
    wfHeap P Gamma' H.
Proof with eauto using wfFields_invariance.
  introv wfP envEquiv wfGamma' wfH.
  inverts wfH as wfGamma envModelsHeap heapMirrorsEnv.
  constructor...
  + introv envLookup. rewrite <- envEquiv in envLookup.
    apply envModelsHeap in envLookup.
    inv envLookup as (F & RL & Hlookup & wfF)...
  + introv Hlookup. rewrite <- envEquiv...
Qed.

(*
--------
wfVars
--------
*)

Hint Constructors wfVars.

Lemma wfVars_invariance :
  forall P t' Gamma Gamma' fsyms V,
    wfProgram P t' ->
    (forall x, Gamma x = Gamma' x) ->
    wfEnv P Gamma' ->
    wfVars P Gamma fsyms V ->
    wfVars P Gamma' fsyms V.
Proof with eauto.
  introv wfP envEquiv wfGamma' wfV.
  inverts wfV as wfGamma envModelsVars varsMirrorEnv Hfresh.
  constructor...
  + introv Vlookup.
    rewrite <- envEquiv in Vlookup.
    apply envModelsVars in Vlookup as (v & Vlookup & hasType).
    eapply hasType_subsumption with (Gamma' := Gamma') in hasType; crush...
  + introv. rewrite <- envEquiv...
Qed.

Lemma wfVars_extend :
  forall P t' Gamma n m V v t,
    wfProgram P t' ->
    wfVars P Gamma n V ->
    P; Gamma |- EVal v \in t ->
    m < n ->
    wfVars P (extend Gamma (env_var (DV (DVar m))) t)
           n (extend V (DVar m) v).
Proof with eauto with env.
  introv wfP wfV hasType Hlt.
  inverts wfV as wfGamma envModelsVars varsMirrorEnv Hfresh.
  constructor; eauto 3 with env.
  + introv envLookup.
    destruct (id_eq_dec (DVar m) x).
    - subst. simpl_extend_hyp.
      inv_eq.
      exists v.
      split...
      inv hasType...
    - rewrite extend_neq in envLookup...
      apply envModelsVars in envLookup as (v' & Vlookup & hasType').
      exists v'.
      split...
      inv hasType'...
  + introv Hle. unfold fresh.
    assert (m < n')
        by omega.
    case_extend; [inv_eq | apply Hfresh]; omega.
Qed.

Lemma wfVars_heapExtend :
  forall Gamma P t' n V l c,
    wfProgram P t' ->
    wfVars P Gamma n V ->
    fresh Gamma (env_loc l) ->
    wfType P (TClass c) ->
    wfVars P (extend Gamma (env_loc l) (TClass c)) n V.
Proof with eauto with env.
  introv wfP wfV Hfresh wfT.
  inverts wfV as wfGamma envModelsVars varsMirrorEnv freshVars.
  constructor...
  + introv envLookup.
    simpl_extend_hyp.
    apply envModelsVars in envLookup as (v & Vlookup & hasType).
    exists v.
    split...
    inv hasType...
Qed.

Lemma wfVars_ge :
  forall P Gamma n V m,
    wfVars P Gamma n V ->
    n <= m ->
    wfVars P Gamma m V.
Proof with eauto.
  introv wfV Hge.
  inverts wfV as wfGamma envModels varsMirror Hfresh.
  econstructor...
  introv Hle.
  assert (n <= n') by omega...
Qed.

(*
----------
wfLocking
----------
*)

Hint Constructors wfHeldLocks.
Hint Constructors wfLocks.
Hint Constructors disjointLocks.
Hint Constructors wfLocking.

Lemma wfHeldLocks_heapExtend :
  forall H Ls c F RL,
    wfHeldLocks H Ls ->
    wfHeldLocks (heapExtend H (c, F, RL)) Ls.
Proof with eauto.
  introv wfLs.
  constructor.
  induction wfLs as [wfLs]...
  rewrite Forall_forall in wfLs.
  apply Forall_forall.
  introv HIn.
  apply wfLs in HIn as [].
  assert (Hlt: l < length H) by
      (eapply heapLookup_lt; eauto)...
  econstructor...
  rewrite heapExtend_lookup_nlen...
  omega.
Qed.

Lemma wfLocking_heapExtend :
  forall H T c F RL,
    wfLocking H T ->
    wfLocking (heapExtend H (c, F, RL)) T.
Proof with eauto using wfHeldLocks_heapExtend.
  introv wfL.
  induction wfL...
Qed.

Lemma wfHeldLocks_heapUpdate :
  forall H Ls l c F F' L L',
    wfHeldLocks H Ls ->
    heapLookup H l = Some (c, F, L) ->
    (In l Ls -> L' = LLocked) ->
    wfHeldLocks (heapUpdate H l (c, F', L')) Ls.
Proof with eauto.
  introv wfLs Hlookup HRL'.
  induction wfLs as [wfLs]...
  rewrite Forall_forall in wfLs.
  constructors.
  apply Forall_forall.
  introv HIn.
  assert(wfL: wfLock H x)...
  inverts wfL as Hlookup' HRL.
  destruct (id_eq_dec l x).
  + subst. rewrite_and_invert.
    apply HRL' in HIn. subst.
    apply WF_Lock with c0 F'...
    rewrite lookup_heapUpdate_eq...
    apply heapLookup_lt...
  + econstructor...
    rewrite lookup_heapUpdate_neq...
Qed.

Lemma wfLocking_heapUpdate :
  forall H T l c F F' L L',
    wfLocking H T ->
    heapLookup H l = Some (c, F, L) ->
    (In l (heldLocks T) -> L' = LLocked) ->
    wfLocking (heapUpdate H l (c, F', L')) T.
Proof with eauto using wfHeldLocks_heapUpdate.
  introv wfL Hlookup HL.
  induction wfL; simpls...
  crush.
Qed.

Lemma wfHeldLocks_taken :
  forall H Ls l c L F,
    wfHeldLocks H Ls ->
    In l Ls ->
    heapLookup H l = Some (c, F, L) ->
    L = LLocked.
Proof with eauto.
  introv wfLs HIn Hlookup.
  induction wfLs as [wfLs]...
  rewrite Forall_forall in wfLs.
  apply wfLs in HIn. inv HIn.
  rewrite_and_invert...
Qed.

Lemma wfLocks_econtext :
  forall Ls e ctx,
    is_econtext ctx ->
    wfLocks Ls (ctx e) ->
    wfLocks Ls e.
Proof with eauto using in_or_app.
  introv Hctx wfL.
  inv Hctx;
    inverts wfL as Hlocks Hdup;
    simpl in *...
  + eapply NoDup_app in Hdup as []...
  + inv Hdup...
Qed.

Lemma wfLocking_econtext :
  forall ctx H Ls e,
    is_econtext ctx ->
    wfLocking H (T_Thread Ls (ctx e)) ->
    wfLocking H (T_Thread Ls e).
Proof with eauto using wfLocks_econtext.
  introv Hctx wfL.
  inv wfL...
Qed.

Lemma wfLocking_subst :
  forall H Ls e x y,
    wfLocking H (T_Thread Ls e) ->
    wfLocking H (T_Thread Ls (subst x y e)).
Proof with eauto.
  introv wfL.
  inverts wfL as wfLs Hdup wfL wfRl.
  econstructor...
  econstructor...
  + rewrite <- locks_subst...
    inv wfL...
  + rewrite <- locks_subst...
    inv wfL...
Qed.

Lemma locks_static :
  forall e,
    exprStatic e ->
    locks e = nil.
Proof with eauto using app_eq_nil.
  introv Hstatic.
  induction Hstatic; simpl...
  apply app_eq_nil...
Qed.

Lemma wfLocking_static :
  forall H Ls e,
    wfHeldLocks H Ls ->
    NoDup Ls ->
    exprStatic e ->
    wfLocking H (T_Thread Ls e).
Proof with eauto using locks_static.
  introv wfLs Hdup Hstatic.
  assert (HL: locks e = nil)...
  econstructor...
  econstructor; rewrite HL...
  introv HIn... inv HIn.
Qed.

Lemma disjointLocks_commutative :
  forall T1 T2,
    disjointLocks T1 T2 ->
    disjointLocks T2 T1.
Proof with eauto.
  introv Hdisj.
  inv Hdisj. constructors...
Qed.

Lemma disjointLocks_async :
  forall T T1 T2 e,
    disjointLocks T1 T /\
    disjointLocks T2 T
     <->
    disjointLocks (T_Async T1 T2 e) T.
Proof with eauto using in_or_app.
  split.
  + introv Hdisj.
    inverts Hdisj as Hdisj1 Hdisj2.
    inverts Hdisj1. inverts Hdisj2.
    constructor; simpl.
    - introv HIn.
      apply in_app_or in HIn as [|HIn]...
    - introv HIn.
      apply not_in_app...
  + introv Hdisj.
    inverts Hdisj as Hdisj1 Hdisj2.
    simpls.
    splits.
    - constructor...
      introv HIn.
      apply Hdisj2 in HIn...
    - constructor...
      introv HIn.
      apply Hdisj2 in HIn.
      eapply not_in_app in HIn as []...
Qed.

Lemma disjointLocks_leftmost :
  forall T1 T2,
    disjointLocks T1 T2 ->
    disjointLocks (T_EXN (leftmost_locks T1)) T2.
Proof with eauto using in_or_app.
  introv Hdisj.
  induction T1; simpls; inv Hdisj...
  apply IHT1_1.
  econstructor; crush...
Qed.

Lemma wfHeldLocks_app :
  forall H Ls1 Ls2,
    (wfHeldLocks H Ls1 /\ wfHeldLocks H Ls2 <-> wfHeldLocks H (Ls1 ++ Ls2)).
Proof with eauto using in_eq, in_cons.
  split.
  + introv wfLs.
    inverts wfLs as wfLs1 wfLs2.
    constructor.
    apply Forall_app...
    inv wfLs1...
    inv wfLs2...
  + introv wfLs.
    induction Ls1 as [|l]; simpls...
    inverts wfLs as wfLs.
    inverts wfLs as wfL wfLs'.
    assert(wfLs: wfHeldLocks H (Ls1 ++ Ls2))...
    apply IHLs1 in wfLs as [wfLs1 wfLs2]...
    split...
    econstructor...
    econstructor...
    apply Forall_forall.
    rewrite Forall_forall in wfLs'.
    introv HIn.
    assert (HIn': In x (Ls1 ++ Ls2))
      by eauto using in_or_app...
Qed.

Lemma wfHeldLocks_cons :
  forall H Ls l,
    wfHeldLocks H Ls ->
    wfLock H l ->
    wfHeldLocks H (l :: Ls).
Proof with eauto.
  introv wfLs wfL.
  inv wfLs...
Qed.

Lemma wfHeldLocks_leftmost :
  forall H T,
    wfLocking H T ->
    wfHeldLocks H (leftmost_locks T).
Proof with eauto.
  introv wfL.
  induction T; inv wfL...
Qed.

Lemma wfHeldLocks_remove :
  forall H Ls L eq_dec,
    wfHeldLocks H Ls ->
    wfHeldLocks H (remove eq_dec L Ls).
Proof with eauto using wfHeldLocks_cons.
  introv wfLs.
  induction Ls as [| l]...
  inverts wfLs as wfLs.
  inverts wfLs.
  simpl. cases_if...
Qed.

Corollary wfLocking_wfHeldLocks :
  forall H T,
    wfLocking H T ->
    wfHeldLocks H (heldLocks T).
Proof with eauto.
  introv wfL.
  induction T; simpls; inv wfL...
  apply wfHeldLocks_app...
Qed.

(*
----------
wfThreads
----------
*)

Hint Constructors wfThreads.

Corollary wfThreads_wfEnv :
  forall P t' Gamma T t,
    wfProgram P t' ->
    wfThreads P Gamma T t ->
    wfEnv P Gamma.
Proof with eauto with env.
  introv wfP wfT. inv wfT...
Qed.

Hint Immediate wfThreads_wfEnv.

Lemma wfThreads_invariance :
  forall P t' Gamma Gamma' T t,
    wfProgram P t' ->
    (forall x, Gamma x = Gamma' x) ->
    wfThreads P Gamma T t ->
    wfThreads P Gamma' T t.
Proof with eauto using hasType_subsumption,
                       wfEnv_equiv with env.
  introv wfP Hequiv wfT.
  induction wfT...
Qed.

Lemma wfThreads_subsumption :
  forall P t' Gamma Gamma' T t,
    wfProgram P t' ->
    wfSubsumption Gamma Gamma' ->
    wfEnv P Gamma' ->
    wfThreads P Gamma T t ->
    wfThreads P Gamma' T t.
Proof with eauto using hasType_subsumption with env.
  introv wfP wfEnv' Hsub wfT.
  induction wfT...
Qed.

Lemma wfThreads_heapExtend :
  forall P t' Gamma T t c l,
    wfProgram P t' ->
    wfType P (TClass c) ->
    fresh Gamma (env_loc l) ->
    wfThreads P Gamma T t ->
    wfThreads P (extend Gamma (env_loc l) (TClass c)) T t.
Proof with eauto using hasType_extend_loc with env.
  introv wfP wfTy Hfresh wfT.
  generalize dependent t.
  induction T; intros; inv wfT...
Qed.

(*
----------------
wfConfiguration
----------------
*)

Hint Constructors wfConfiguration.

Lemma wfConfiguration_substitution :
  forall P Gamma H V n Ls e e' t,
    freeVars e' = nil ->
    P; Gamma |- e' \in t ->
    wfLocking H (T_Thread Ls e') ->
    wfConfiguration P Gamma (H, V, n, T_Thread Ls e) t ->
    wfConfiguration P Gamma (H, V, n, T_Thread Ls e') t.
Proof with eauto.
  introv Hfree hasType wfL wfCfg.
  inverts wfCfg...
Qed.

Lemma wfConfiguration_heapExtend :
  forall P t' Gamma H V n T t c F L,
    wfProgram P t' ->
    wfConfiguration P Gamma (H, V, n, T) t ->
    wfType P (TClass c) ->
    wfFields P Gamma c F ->
    wfConfiguration P (extend Gamma (env_loc (length H)) (TClass c))
                    ((heapExtend H (c, F, L)), V, n, T) t.
Proof with eauto 6 using
                 wfHeap_extend,
                 wfVars_heapExtend,
                 wfThreads_heapExtend,
                 wfLocking_heapExtend with env.
  introv wfP wfCfg wfTy wfF.
  inverts wfCfg.
  assert(fresh Gamma (env_loc (length H)))
    by eauto using wfHeap_fresh, heapLookup_ge...
Qed.

Lemma wfConfiguration_heapUpdate :
  forall P t' Gamma H V n T t l c F L L' F',
    wfProgram P t' ->
    wfConfiguration P Gamma (H, V, n, T) t ->
    heapLookup H l = Some (c, F, L) ->
    wfFields P Gamma c F' ->
    (In l (heldLocks T) -> L' = LLocked) ->
    wfConfiguration P Gamma
                    ((heapUpdate H l (c, F', L')), V, n, T) t.
Proof with eauto using
                 wfHeap_update,
                 wfLocking_heapUpdate.
  introv wfP wfCfg HLookup wfF' HL.
  inverts wfCfg...
Qed.
