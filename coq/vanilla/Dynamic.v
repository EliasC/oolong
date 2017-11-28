Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import List.

Require Export Syntax.

Reserved Notation " P '/' cfg '==>' cfg' " (at level 40).

Inductive step (P : program) : configuration -> configuration -> Prop :=
(***************)
(* Parallelism *)
(***************)
  | EvalAsyncLeft :
      forall H H' V V' n n' T1 T1' T2 e,
        P / (H, V, n, T1) ==>
          (H', V', n', T1') ->
        P / (H, V, n, T_Async T1 T2 e) ==>
          (H', V', n', T_Async T1' T2 e)
  | EvalAsyncRight :
      forall H H' V V' n n' T1 T2 T2' e,
        P / (H, V, n, T2) ==>
          (H', V', n', T2') ->
        P / (H, V, n, T_Async T1 T2 e) ==>
          (H', V', n', T_Async T1 T2' e)
  | EvalAsyncJoin :
      forall H V n e1 T2 Ls e,
        threads_done(T_Thread Ls e1) ->
        threads_done(T2) ->
        P / (H, V, n, T_Async (T_Thread Ls e1) T2 e) ==>
          (H, V, n, T_Thread Ls e)
  | EvalSpawn :
      forall H V n e1 e2 e3 Ls,
        P / (H, V, n, T_Thread Ls (EPar e1 e2 e3)) ==>
          (H, V, n, T_Async (T_Thread Ls e1) (T_Thread nil e2) e3)
  | EvalSpawnContext :
      forall H V n ctx e e1 e2 e3 Ls,
        is_econtext ctx ->
        P / (H, V, n, T_Thread Ls e) ==>
          (H, V, n, T_Async (T_Thread Ls e1) (T_Thread nil e2) e3) ->
        P / (H, V, n, T_Thread Ls (ctx e)) ==>
          (H, V, n, T_Async (T_Thread Ls e1) (T_Thread nil e2) (ctx e3))
(*****************)
(* Single thread *)
(*****************)
  | EvalContext :
      forall H H' V V' n n' ctx e e' Ls Ls',
        is_econtext ctx ->
        P / (H, V, n, T_Thread Ls e) ==>
          (H', V', n', T_Thread Ls' e') ->
        P / (H, V, n, T_Thread Ls (ctx e)) ==>
          (H', V', n', T_Thread Ls' (ctx e'))
  | EvalVar :
      forall H V n x v Ls,
        V x = Some v ->
        P / (H, V, n, T_Thread Ls (EVar (DV x))) ==>
          (H, V, n, T_Thread Ls (EVal v))
  | EvalCast :
      forall H V n v t Ls,
        P / (H, V, n, T_Thread Ls (ECast t (EVal v))) ==>
          (H, V, n, T_Thread Ls (EVal v))
  | EvalNew :
      forall H V n c i fs ms Ls,
        classLookup P c = (Some (Cls c i fs ms)) ->
        P / (H, V, n, T_Thread Ls (ENew c)) ==>
          (heapExtend H (c, declsToFields fs, LUnlocked),
           V, n, T_Thread Ls (EVal (VLoc (length H))))
  | EvalCall :
      forall H V n x l m v c mtds y body t t' Ls,
        V x = Some (VLoc l) ->
        (exists F RL, heapLookup H l = Some (c, F, RL)) ->
        methods P (TClass c) = Some mtds ->
        methodLookup mtds m = Some (Method m (y, t) t' body) ->
        P / (H, V, n, T_Thread Ls (ECall (DV x) m (EVal v))) ==>
          (H, extend (extend V (DVar n) (VLoc l)) (DVar (S n)) v, S (S n),
           T_Thread Ls (subst y (DVar (S n)) (subst this (DVar n) body)))
  | EvalSelect :
      forall H V n x l f c F RL v Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        F f = Some v ->
        P / (H, V, n, T_Thread Ls (ESelect (DV x) f)) ==>
          (H, V, n, T_Thread Ls (EVal v))
  | EvalUpdate :
      forall H V n x l f v c F RL Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, RL) ->
        P / (H, V, n, T_Thread Ls (EUpdate (DV x) f (EVal v))) ==>
          (heapUpdate H l (c, extend F f v, RL), V, n, T_Thread Ls (EVal VNull))
  | EvalLet :
      forall H V n x v body Ls,
        P / (H, V, n, T_Thread Ls (ELet x (EVal v) body)) ==>
          (H, extend V (DVar n) v, S n, T_Thread Ls ((subst x (DVar n) body)))
(***********)
(* Locking *)
(***********)
  | EvalLock :
      forall H V n x l e c F Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, LUnlocked) ->
        ~ In l Ls ->
        P / (H, V, n, T_Thread Ls (ELock (DV x) e)) ==>
          (heapUpdate H l (c, F, LLocked), V, n, T_Thread (l :: Ls) (ELocked l e))
  | EvalLock_Reentrant :
      forall H V n x l e c F Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, LLocked) ->
        In l Ls ->
        P / (H, V, n, T_Thread Ls (ELock (DV x) e)) ==>
          (H, V, n, T_Thread Ls e)
  | EvalLock_Release :
      forall H V n l v c F Ls,
        heapLookup H l = Some (c, F, LLocked) ->
        In l Ls ->
        P / (H, V, n, T_Thread Ls (ELocked l (EVal v))) ==>
          (heapUpdate H l (c, F, LUnlocked), V, n, T_Thread (remove id_eq_dec l Ls) (EVal v))
(**************)
(* Exceptions *)
(**************)
  | EvalEXN_AsyncLeft :
      forall H V n T1 T2 e,
        threads_exn(T1) ->
        P / (H, V, n, T_Async T1 T2 e) ==>
          (H, V, n, T_EXN (leftmost_locks T1))
  | EvalEXN_AsyncRight :
      forall H V n T1 T2 e,
        threads_exn(T2) ->
        P / (H, V, n, T_Async T1 T2 e) ==>
          (H, V, n, T_EXN (leftmost_locks T1))
  | EvalEXN_Context :
      forall ctx H V n e Ls,
        is_econtext ctx ->
        P / (H, V, n, T_Thread Ls e) ==>
           (H, V, n, T_EXN Ls) ->
        P / (H, V, n, T_Thread Ls (ctx e)) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_Call :
      forall H V n x m v Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (ECall (DV x) m (EVal v))) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_Select :
      forall H V n x f Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (ESelect (DV x) f)) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_Update :
      forall H V n x f v Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (EUpdate (DV x) f (EVal v))) ==>
          (H, V, n, T_EXN Ls)
  | EvalEXN_Lock :
      forall H V n x e Ls,
        V x = Some VNull ->
        P / (H, V, n, T_Thread Ls (ELock (DV x) e)) ==>
          (H, V, n, T_EXN Ls)
  where " P '/' cfg '==>' cfg' " := (step P cfg cfg').

Hint Constructors step.

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "EvalAsyncLeft"
  | Case_aux c "EvalAsyncRight"
  | Case_aux c "EvalAsyncJoin"
  | Case_aux c "EvalSpawn"
  | Case_aux c "EvalSpawnContext"

  | Case_aux c "EvalContext"
  | Case_aux c "EvalVar"
  | Case_aux c "EvalNew"
  | Case_aux c "EvalCall"
  | Case_aux c "EvalSelect"
  | Case_aux c "EvalUpdate"
  | Case_aux c "EvalLet"

  | Case_aux c "EvalLock"
  | Case_aux c "EvalLock_Reentrant"
  | Case_aux c "EvalLock_Release"

  | Case_aux c "EvalEXN_AsyncLeft"
  | Case_aux c "EvalEXN_AsyncRight"
  | Case_aux c "EvalEXN_Context"
  | Case_aux c "EvalEXN_Call"
  | Case_aux c "EvalEXN_Select"
  | Case_aux c "EvalEXN_Update"
  ].

Definition multistep (P : program) := clos_refl_trans_1n configuration (step P).
Notation " P '/' cfg '==>*' cfg' " := (multistep P cfg cfg') (at level 40).

Inductive cfg_blocked : configuration -> Prop :=
  | Blocked_Deadlock :
      forall H V n T1 T2 e,
        cfg_blocked (H, V, n, T1) ->
        cfg_blocked (H, V, n, T2) ->
        cfg_blocked (H, V, n, T_Async T1 T2 e)
  | Blocked_Left :
      forall H V n T1 T2 e,
        cfg_blocked (H, V, n, T1) ->
        threads_done T2 ->
        cfg_blocked (H, V, n, T_Async T1 T2 e)
  | Blocked_Right :
      forall H V n T1 T2 e,
        threads_done T1 ->
        cfg_blocked (H, V, n, T2) ->
        cfg_blocked (H, V, n, T_Async T1 T2 e)
  | Blocked_W :
      forall H V n x e l c F Ls,
        V x = Some (VLoc l) ->
        heapLookup H l = Some (c, F, LLocked) ->
        ~ In l Ls ->
        cfg_blocked (H, V, n, T_Thread Ls (ELock (DV x) e))
  | Blocked_Context :
      forall H V n ctx e Ls,
        is_econtext ctx ->
        cfg_blocked (H, V, n, T_Thread Ls e) ->
        cfg_blocked (H, V, n, T_Thread Ls (ctx e)).
