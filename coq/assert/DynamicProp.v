Require Import SyntaxProp.
Require Export Dynamic.
Require Import Shared.

(*
=====
step
=====
*)

Lemma step_n_monotonic :
  forall P H H' V V' n n' T T',
    P / (H, V, n, T) ==> (H', V', n', T') ->
    n <= n'.
Proof with eauto.
  introv Hstep.
  gen T'.
  induction T as [| |]; intros; inv Hstep...
  gen e'.
  induction e0; introv Hstep;
  inv Hstep; try(malformed_context);
  try(inv_eq)...
Qed.
