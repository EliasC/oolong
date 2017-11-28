Require Import MetaProp.
Require Import SyntaxProp.
Require Import DynamicProp.
Require Import TypesProp.
Require Import WellFormednessProp.
Require Import Shared.
Require Import Locking.

Hint Constructors is_econtext.
Hint Constructors cfg_blocked.

Tactic Notation "preservation_context_tactic" integer(n) :=
  solve[
      intuition;
         match goal with
           | [IH : forall cfg', _ / ?cfg ==> cfg' -> ?P,
                Hstep : _ / ?cfg ==> _ |- _] =>
             eapply IH in Hstep as (Gamma' & wfCfg' & Hsub);
               eauto;
               inverts wfCfg' as Hfresh' wfH' wfV' wfT';
               inversion wfT'; inversion Hsub;
               exists Gamma'; split; try(eassumption)
         end;
         repeat (econstructor;
                 simpl;
                 eauto n using hasType_subsumption,
                               hasType_subsumption_extend
                          with env); try(omega)
    | eexists; split; eauto with env].

Hint Immediate lt_0_Sn.

Lemma single_threaded_preservation :
  forall P t' Gamma H V n Ls e cfg' t,
    wfProgram P t' ->
    wfConfiguration P Gamma (H, V, n, T_Thread Ls e) t ->
    P / (H, V, n, T_Thread Ls e) ==> cfg' ->
    exists Gamma',
      wfConfiguration P Gamma' cfg' t /\
      wfSubsumption Gamma Gamma'.
Proof with eauto using subtypeOf with env.
  introv wfP wfCfg Hstep.
  inverts wfCfg as Hfresh wfH wfV wfT wfL.
  inverts wfT as Hfree hasType.
  gen cfg'.
  hasType_cases(induction hasType) Case; intros;
  (* Some trivial cases can be discarded*)
  try(inv Hstep; malformed_context);

  (* All variables must be dynamic *)
  match goal with
    | [Hfree : freeVars _ = nil |- _] =>
      simpl in Hfree;
        repeat
        match goal with
          | [Hfree : freeVars _ ++ _ ++ _ = nil |- _] =>
            simpl in Hfree;
              apply app_eq_nil in Hfree as (Hfree1 & Hfree2);
              apply app_eq_nil in Hfree2 as (Hfree2 & Hfree3)
          | [Hfree : freeVars _ ++ _ = nil |- _] =>
            simpl in Hfree;
              apply app_eq_nil in Hfree as (Hfree1 & Hfree2)
          | [x : var |- _] =>
            destruct x; try(congruence)
        end
    | _ => idtac
  end;

  (* Unfold the resulting configuation *)
  destruct cfg' as [[[H' V'] n'] T'];

  (* Assert that the fresh symbols grow monotonically *)
  assert (Hmono: n <= n')
    by eauto using step_n_monotonic;
  try(
  assert (wfL': wfLocking H' T')
    by (eapply wfLocking_preservation in Hstep; eauto)
    ).
  + Case "T_Var".
    inverts Hstep; try malformed_context...
    wfEnvLookup. rewrite_and_invert.
    eexists...
  + Case "T_New".
    inv Hstep; try malformed_context.
    exists (extend Gamma (env_loc (length H)) (TClass c)).
    assert (wfEnv P (extend Gamma (env_loc (length H)) (TClass c)))...
    assert (fresh Gamma (env_loc (length H)))...
    split...
    apply wfConfiguration_substitution
    with (ENew c); eauto using subtypeOf, wfLocking_heapExtend.
    eapply wfConfiguration_heapExtend;
      eauto using wfFields_declsToFields.
    eapply wfRegionLocks_declsToRegionLocks; crush.
  + Case "T_Call".
    assert (wfL'': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalCall". clear IHhasType.
      assert(Hsub: subtypeOf P (TClass c) t1)
      by (wfEnvLookup; rewrite_and_invert;
          inv hasType0; wfEnvLookup;
          assert (c0 = c) by crush; subst; eauto).

      assert (wfC: wfType P (TClass c))...
      assert (cLookup: classLookup P c <> None)
        by (inv wfC; assumption).
      apply classLookup_not_none in cLookup as (i & fs & ms & cLookup).
      assert (wfCls: wfClassDecl P (Cls c i fs ms))
        by (inv wfP; lookup_forall as wfCls; eauto)...
      assert (mtds = ms)
        by (simpls; destruct classLookup; eauto; inv_eq; inv_eq).
      subst.
      inverts wfCls as Hsigs wfFlds wfMtds.

      assert (wfT2: wfType P t2)...
      assert (sigLookup: methodSigLookup (extractSigs ms) m = Some (MethodSig m (y, t2) t))
        by eauto using methodSigs_sub.
      apply extractSigs_sound in sigLookup as [e mLookup].
      rewrite_and_invert.
      exists (extend
                (extend
                   Gamma (env_var (DV (DVar n))) (TClass c))
                (env_var (DV (DVar (S n)))) t2).
      assert (fresh Gamma (env_var (DV (DVar n))))...
      assert (n <= S n)...
      assert (fresh Gamma (env_var (DV (DVar (S n)))))...
      split...
      * { econstructor; auto.
          + eapply wfHeap_invariance
            with (Gamma := Gamma); eauto 3 with env.
          + eapply wfVars_extend; eauto 2 with env.
            - eapply wfVars_extend...
              apply wfVars_ge with n...
            - eapply hasType_subsumption
              with (Gamma := Gamma);
              eauto 2 using wfSubsumption_fresh with env.
          + lookup_forall as wfMtd.
            inv wfMtd. simpls.
            econstructor...
            - autorewrite with freeVars...
            - eapply hasType_subst; eauto 3 with env.
              eapply hasType_flip...
              eapply hasType_subst; eauto 3 with env.
              eapply hasType_subsumption
              with (Gamma := (extend
                                (extend empty (env_var (SV y)) t2)
                                 (env_var (SV this)) (TClass c)));
                eauto 3 using wfSubsumption_extend with env.
              unfold fresh. case_extend. inv_eq. omega.
        }
  + Case "T_Select".
    inv hasType.
    assert (wfType P t)
      by eauto using fieldLookup_wfType.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalSelect". clear IHhasType.
      wfEnvLookup. rewrite_and_invert.
      inverts hasType as Vlookup envLookup Hsub.
      assert (t2 = TClass c); subst...
      assert (c0 = c)
        by (wfEnvLookup; rewrite_and_invert); subst.
      assert (wfF: exists v, F f = Some v /\
                             P; Gamma |- EVal v \in t)
        by eauto using dyn_wfFieldLookup, wfHeap_wfFields.
      inv wfF as (v' & Flookup & hasType).
      rewrite_and_invert.
      inv wfL.
      eexists. split...
  + Case "T_Update".
    assert (wfL'': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalUpdate". clear IHhasType1. clear IHhasType2.
      inv hasType1. wfEnvLookup. rewrite_and_invert.
      inv hasType. wfEnvLookup.
      assert (Heq: TClass c1 = TClass c)... inv Heq.
      rewrite_and_invert.
      exists Gamma. split...
      inverts wfL as ? ? wfL.
      inv wfL...
      eapply wfConfiguration_heapUpdate;
        eauto using wfFields_extend, wfHeldLocks_taken;
        crush.
  + Case "T_Let".
    assert (wfL': wfLocking H' T').
      eapply wfLocking_preservation in Hstep...
      econstructor...
      econstructor...
      simpl...
    assert (wfLocking H (T_Thread Ls e))
      by (apply wfLocking_econtext with (ctx := ctx_let x body); eauto).
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalLet". clear IHhasType1. clear IHhasType2.
      exists (extend Gamma (env_var (DV (DVar n))) t).
      split...
      * { econstructor; auto.
          + eapply wfHeap_invariance
            with (Gamma := Gamma);
            eauto 2 with env.
          + eapply wfVars_extend...
            eapply wfVars_ge...
          + econstructor;
            eauto using hasType_subst with env;
            autorewrite with freeVars...
        }
      * apply wfSubsumption_fresh...
  + Case "T_Cast".
    assert (wfL'': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalCast". clear IHhasType.
      exists Gamma. split...
      econstructor...
      econstructor...
      inv hasType...
  + Case "T_Par".
    assert (wfL': wfLocking H' T').
      eapply wfLocking_preservation in Hstep...
      econstructor...
      econstructor...
      simpl... crush.
    inv Hstep; try(malformed_context).
    exists Gamma.
    split...
    econstructor...
    apply wfSubsumption_frame in H0 as []...
    econstructor...
    - econstructor...
      eapply hasType_subsumption with (Gamma := Gamma1)...
    - econstructor...
      eapply hasType_subsumption with (Gamma := Gamma2)...
  + Case "T_Lock".
    inv hasType1.
    wfEnvLookup.
    inv hasType.
    - SCase "V x = l".
      inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2);
      rewrite_and_invert.
      exists Gamma. split...
      econstructor...
      eapply wfHeap_update...
      * eapply wfHeap_wfFields...
      * eapply wfHeap_wfRegionLocks with (P := P) in H20 as []...
        econstructor...
    - inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2);
      rewrite_and_invert.
  + Case "T_Locked".
    inv hasType1.
    assert (wfL'': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv Hstep;
      try(malformed_context); try(inv_eq);
      try(preservation_context_tactic 2).
    - SCase "EvalLock_Release". clear IHhasType1. clear IHhasType2.
      exists Gamma. split...
      econstructor...
      eapply wfHeap_update...
      * eapply wfHeap_wfFields...
      * eapply wfHeap_wfRegionLocks with (P := P) in H7 as []...
        econstructor...
Qed.

Theorem preservation :
  forall P t' Gamma cfg cfg' t,
    wfProgram P t' ->
    wfConfiguration P Gamma cfg t ->
    P / cfg ==> cfg' ->
    exists Gamma',
      wfConfiguration P Gamma' cfg' t /\
      wfSubsumption Gamma Gamma'.
Proof with eauto using wfConfiguration.
  introv wfP wfCfg Hstep.
  inverts wfCfg as Hfresh wfH wfV wfT wfL.
  gen t cfg' wfL wfT.
  induction T; intros...
  + Case "T = EXN".
    (* EXN does not step *)
    inv Hstep.
  + Case "T = T_Thread e".
    eapply single_threaded_preservation...
  + Case "T = T_Async T1 T2 e".
    inverts wfT as Hfree hasType wfT1 wfT2.
    inverts wfL as wfWl wfRl Hdisj wfL1 wfL2.
    destruct cfg' as [[[H' V'] n'] T'].
    assert (Hmono: n <= n')
      by eauto using step_n_monotonic.
    assert(wfLocking H' T')
      by eauto using wfLocking_preservation.
    inv Hstep;
    try(
        solve
          [
            (* When no thread steps, Gamma still types the cfg *)
            exists Gamma; split; eauto with env
          |
            (* When one of the threads step, IH applies *)
            match goal with
              | [IH: forall t cfg', _ / (_, _, _, ?T) ==> cfg' -> _,
                   Hstep: _ / (_, _, _, ?T) ==> _ |- _]
                => eapply IH in Hstep as [Gamma' [wfCfg' wfSub]];
                  eauto; inverts wfCfg'; exists Gamma'
            end;
            split; eauto;
            econstructor; eauto with arith;
            econstructor;
            eauto using hasType_subsumption,
                        wfThreads_subsumption
          ]).
Qed.
