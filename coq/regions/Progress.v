Require Import MetaProp.
Require Import SyntaxProp.
Require Import DynamicProp.
Require Import TypesProp.
Require Import WellFormednessProp.
Require Import Shared.

Hint Constructors is_econtext.
Hint Constructors cfg_blocked.

Lemma exists_declsToRegionLocks :
  forall fs,
    exists RL, declsToRegionLocks fs RL.
Proof with eauto.
  introv. induction fs as [| [f t r] fs' IH].
  + exists (empty (A := region_id) (B := lock_status)).
    econstructor.
    introv fLookup.
    simpl in fLookup...
  + destruct IH as [RL H].
    exists (extend RL r LUnlocked).
    econstructor.
    introv fLookup.
    simpl in fLookup.
    remember (beq_nat f0 f) as fEq.
    destruct fEq.
    - inv_eq.
    - case_extend.
      inv H...
Qed.

Lemma single_threaded_progress :
  forall P t' Gamma H V n Ls e t,
    wfProgram P t' ->
    wfConfiguration P Gamma (H, V, n, T_Thread Ls e) t ->
    threads_done (T_Thread Ls e) \/
    cfg_blocked (H, V, n, T_Thread Ls e) \/
    exists cfg', P / (H, V, n, T_Thread Ls e) ==> cfg'.
Proof with eauto using step.
  introv wfP wfCfg.
  inverts wfCfg as Hfresh wfH wfV wfT wfL.
  inverts wfT as Hfree hasType wfLs wfL.
  hasType_cases(induction hasType) Case;

    (* All non-trivial cases step *)
    simpl; try(solve[eauto]); right;

    (* All variables must be dynamic *)
    match goal with
      | [Hfree : freeVars _ = nil |- _] =>
        simpl in Hfree;
          repeat
          match goal with
           | [Hfree : freeVars _ ++ _ = nil |- _] =>
             simpl in Hfree;
             apply app_eq_nil in Hfree as [Hfree1 Hfree2]
           | [x : var |- _] =>
             destruct x; try(congruence)
          end
      | _ => idtac
    end;

    (* If there's a target x, invert its typing derivation*)
    repeat
    match goal with
      | [H : Types.hasType ?P ?Gamma (EVar (DV ?x)) _ |- _ ] =>
        inv H
      | _ => idtac
    end;

    (* Each variable lookup in Gamma corresponds to some lookup in V *)
    repeat wfEnvLookup...
  + Case "T_New".
    right.
    assert (cLookup: exists i fs ms, classLookup P c = Some (Cls c i fs ms))
      by eauto using classLookup_not_none.
    destruct cLookup as (i & fs & ms & cLookup).
    assert(exRL: exists RL, declsToRegionLocks fs RL) by
        eauto using exists_declsToRegionLocks.
    destruct exRL as [RL].
    eexists; eapply EvalNew...
  + Case "T_Call".
    assert (wfL': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    assert (IH: threads_done (T_Thread Ls e) \/
                cfg_blocked (H, V, n, T_Thread Ls e) \/
                exists cfg', P / (H, V, n, T_Thread Ls e) ==> cfg')...
    inv IH as [edone | [eBlocked | eSteps]]...
    - SCase "e done".
      right.
      destruct e; try(contradiction).
      inv hasType0...
      wfEnvLookup.
      assert (wfC: wfType P (TClass c))...
      inverts wfC as cLookup.
      apply classLookup_not_none in cLookup as (i & fs & ms & cLookup).
      assert (Hsigs: methodSigLookup (extractSigs ms) m = Some (MethodSig m (y, t2) t))
        by eauto using methodSigs_sub.
      eapply extractSigs_sound in Hsigs as [e mLookup].
      assert (methods P (TClass c) = Some ms)
        by (simpl; rewrite cLookup; eauto).
      eexists; eapply EvalCall...
    - SCase "e can step".
      destruct eSteps as [[[[H' V'] n'] T'] eSteps].
      destruct T'...
      inv eSteps...
      inv eSteps...
  + Case "T_Select".
    right.
    inv hasType...
    assert (t2 = TClass c)...
    wfEnvLookup.
    eapply dyn_wfFieldLookup in wfF as [v []]...
    eexists. eapply EvalSelect...
  + Case "T_Update".
    assert (wfL': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    assert (IH: threads_done (T_Thread Ls e) \/
                cfg_blocked (H, V, n, T_Thread Ls e) \/
                exists cfg', P / (H, V, n, T_Thread Ls e) ==> cfg')...
    inv IH as [edone | [eBlocked | eSteps]]...
    - SCase "e done".
      destruct e; try(contradiction)...
      inv hasType...
      wfEnvLookup...
    - SCase "e can step".
      destruct eSteps as [[[[H' V'] n'] T'] eSteps].
      destruct T'...
      inv eSteps...
      inv eSteps...
  + Case "T_Let".
    remember (fun e : expr => ELet x e body) as ctx.
    assert (is_econtext ctx). subst. apply EC_Let.
    assert (wfL': wfLocking H (T_Thread Ls e))
      by (apply wfLocking_econtext with ctx; crush).
    replace (ELet x e body) with (ctx e) by crush...
    assert (IH: threads_done (T_Thread Ls e) \/
                cfg_blocked (H, V, n, T_Thread Ls e) \/
                exists cfg', P / (H, V, n, T_Thread Ls e) ==> cfg')...
    inversion IH as [edone | [eBlocked | eSteps]]...
    - SCase "e done".
      subst.
      destruct e; try(contradiction)...
    - SCase "e can step".
      destruct eSteps as [[[[H' V'] n'] T'] eSteps].
      destruct T'...
      inverts eSteps...
      inverts eSteps...
  + Case "T_Cast".
    assert (wfL': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    assert (IH: threads_done (T_Thread Ls e) \/
                cfg_blocked (H, V, n, T_Thread Ls e) \/
                exists cfg', P / (H, V, n, T_Thread Ls e) ==> cfg')...
    inv IH as [edone | [eBlocked | eSteps]]...
    - SCase "e done".
      destruct e; try(contradiction)...
    - SCase "e can step".
      destruct eSteps as [[[[H' V'] n'] T'] eSteps].
      destruct T'...
      inverts eSteps...
      inverts eSteps...
  + Case "T_Lock".
    destruct v...
    inv hasType.
    wfEnvLookup.
    assert (TClass c = t2)
      by (unfold fields in *; destruct t2; eauto).
    subst.
    assert(Hex: exists status, RL r = Some status).
      inv wfRL... rewrite_and_invert.
      destruct H1 as (f & t'' & fLookup)...
    inv Hex as [status RLlookup].
    assert(HIn: {In (l, r) Ls} + {~ In (l, r) Ls})
      by (apply in_dec; apply id_eq_dec).
    assert(wfLs: wfHeldLocks H Ls)
      by (inv wfL; eauto).
    destruct status; destruct HIn as [HIn|HnotIn]...
    eapply wfHeldLocks_taken in HIn...
    rewrite_and_invert.
  + Case "T_Locked".
    assert (wfL': wfLocking H (T_Thread Ls e))
      by eauto 3 using wfLocking_econtext.
    inv hasType1.
    wfEnvLookup.
    assert (HIn: In (l, r) Ls) by
      (inverts wfL as _ _ []; simpls; eauto).
    assert (Hlocked: RL r = Some LLocked)
      by (inv wfL; eauto using wfHeldLocks_taken).
    assert (IH: threads_done (T_Thread Ls e) \/
                cfg_blocked (H, V, n, T_Thread Ls e) \/
                exists cfg', P / (H, V, n, T_Thread Ls e) ==> cfg')...
    inv IH as [edone | [eBlocked | eSteps]]...
    - SCase "e done".
      destruct e; try(contradiction)...
    - destruct eSteps as [[[[H' V'] n'] T'] eSteps].
      destruct T'...
      inverts eSteps...
      inverts eSteps...
Qed.

Theorem progress :
  forall P t' Gamma cfg t,
    wfProgram P t' ->
    wfConfiguration P Gamma cfg t ->
    cfg_exn cfg \/ cfg_done cfg \/ cfg_blocked cfg \/
    exists cfg', P / cfg ==> cfg'.
Proof with eauto.
  introv wfP wfCfg.
  inverts wfCfg as Hfresh wfH wfV wfT wfL.
  gen t.
  induction T; intros; simpl...
  + Case "T = Thread".
    right. eapply single_threaded_progress...
  + Case "T = Async T1 T2 e".
    inverts wfT as Hfree hasType wfT1 wfT2.
    inverts wfL as wfL HL Hdisj wfL1 wfL2.
    right. right.
    pose proof (IHT1 wfL1 t1 wfT1) as IH1.
    pose proof (IHT2 wfL2 t2 wfT2) as IH2.
    destruct IH1 as [T1EXN|[T1Done|[T1Blocked|T1Steps]]]...
    - SCase "T1 done".
      unfolds in T1Done. unfold threads_done in T1Done.
      destruct T1; try(solve[inv T1Done]).
      destruct IH2 as [T2EXN|[T2Done|[T2Blocked|T2Steps]]]...
      * SSCase "T2 steps".
        destruct T2Steps as [[[[H' V'] n'] T2']].
        right. eexists; eapply EvalAsyncRight...
    - SCase "T1 blocked".
      destruct IH2 as [T2EXN|[T2Done|[T2Blocked|T2Steps]]]...
      * SSCase "T2 steps".
        destruct T2Steps as [[[[H' V'] n'] T2']].
        right. eexists; eapply EvalAsyncRight...
    - SCase "T1 steps".
      destruct T1Steps as [[[[H' V'] n'] T2']].
      right. eexists; eapply EvalAsyncLeft...
Qed.
