Require Import DynamicProp.
Require Import TypesProp.
Require Import WellFormednessProp.
Require Import Progress.
Require Import Preservation.
Require Import Shared.

Theorem type_soundness :
  forall P t' Gamma cfg t cfg',
    wfProgram P t' ->
    wfConfiguration P Gamma cfg t ->
    P / cfg ==>* cfg' ->
    (exists Gamma',
       wfConfiguration P Gamma' cfg' t /\
       wfSubsumption Gamma Gamma'
    ) /\
    (cfg_exn(cfg') \/ cfg_done(cfg') \/
     cfg_blocked(cfg') \/
     exists cfg'', P / cfg' ==> cfg'').
Proof with eauto with env.
  introv wfP wfCfg HstepMulti.
  split.
  + Case "Preservation".
    gen Gamma.
    induction HstepMulti as [cfg|cfg cfg' cfg'' Hstep]; intros.
    - SCase "cfg = cfg'".
      exists Gamma...
    - SCase "cfg ==> cfg'".
      eapply preservation in Hstep
        as (Gamma' & wfCfg' & HSub)...
      apply IHHstepMulti in wfCfg'
        as (Gamma'' & wfCfg'' & HSub').
      exists Gamma''. split...
      eapply wfSubsumption_trans...
  + Case "Progress".
    gen Gamma.
    induction HstepMulti as [cfg|cfg cfg' cfg'' Hstep]; intros.
    - SCase "cfg = cfg'".
      eapply progress in wfCfg...
    - SCase "cfg ==> cfg'".
      eapply preservation in Hstep
        as (Gamma' & wfCfg' & HSub)...
Qed.
