Require Import List.
Import ListNotations.

Require Export Meta.
Require Export Shared.

(*
======
Types
======
*)

Inductive ty : Type :=
  | TClass : class_id -> ty
  | TInterface : interface_id -> ty
  | TUnit : ty.

(*
============
Expressions
============
*)

Inductive val : Type :=
  | VNull : val
  | VLoc  : loc -> val.

Inductive var : Type :=
  | SV : svar -> var
  | DV : dvar -> var.

Inductive expr : Type :=
  | EVal : val -> expr
  | EVar : var -> expr
  | ENew : class_id -> expr
  | ECall : var -> method_id -> expr -> expr
  | ESelect : var -> field_id -> expr
  | EUpdate : var -> field_id -> expr -> expr
  | ELet : svar -> expr -> expr -> expr
  | ECast : ty -> expr -> expr
  | EPar : expr -> expr -> expr -> expr
  | ELock : var -> region_id -> expr -> expr
  | ELocked : lock -> expr -> expr
.

Tactic Notation "expr_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "EVal"
  | Case_aux c "EVar"
  | Case_aux c "ENew"
  | Case_aux c "ECall"
  | Case_aux c "ESelect"
  | Case_aux c "EUpdate"
  | Case_aux c "ELet"
  | Case_aux c "ECast"
  | Case_aux c "EPar"
  | Case_aux c "ELock"
  | Case_aux c "ELocked"
].

Definition econtext := expr -> expr.

Definition ctx_call (x : _) (m : _) : econtext := (fun e => ECall x m e).
Hint Unfold ctx_call.
Definition ctx_update (x : _) (f : _) : econtext := (fun e => EUpdate x f e).
Hint Unfold ctx_update.
Definition ctx_let (x : _) (body : _) : econtext := (fun e => ELet x e body).
Hint Unfold ctx_let.
Definition ctx_cast (t : _) : econtext := (fun e => ECast t e).
Hint Unfold ctx_cast.
Definition ctx_locked (L : _) : econtext := (fun e => ELocked L e).
Hint Unfold ctx_locked.

Inductive is_econtext : econtext -> Prop :=
  | EC_Call :
      forall x m,
        is_econtext (ctx_call x m)
  | EC_Update :
      forall x f,
        is_econtext (ctx_update x f)
  | EC_Let :
      forall x body,
        is_econtext (ctx_let x body)
  | EC_Cast :
      forall t,
        is_econtext (ctx_cast t)
  | EC_Locked :
      forall L,
        is_econtext (ctx_locked L).

Definition isVal (e : expr) : Prop :=
  match e with
    | EVal _ => True
    | _ => False
  end.

Inductive exprStatic : expr -> Prop :=
  | StaticVar : forall x, exprStatic (EVar (SV x))
  | StaticNull : exprStatic (EVal VNull)
  | StaticNew : forall c, exprStatic (ENew c)
  | StaticCall : forall x m arg, exprStatic arg -> exprStatic (ECall (SV x) m arg)
  | StaticSelect : forall x f, exprStatic (ESelect (SV x) f)
  | StaticUpdate : forall x f e, exprStatic e -> exprStatic (EUpdate (SV x) f e)
  | StaticLet : forall x e body, exprStatic e -> exprStatic body -> exprStatic (ELet x e body)
  | StaticPar : forall e1 e2 e3, exprStatic e1 -> exprStatic e2 -> exprStatic e3 -> exprStatic (EPar e1 e2 e3)
  | StaticCast : forall t e, exprStatic e -> exprStatic (ECast t e)
  | StaticLock : forall x r e, exprStatic e -> exprStatic (ELock (SV x) r e)
.

Fixpoint freeVars (e : expr) : list svar :=
  match e with
    | EVar (SV x) => [x]
    | ECall (SV x) _ arg => x :: (freeVars arg)
    | ECall (DV _) _ arg => (freeVars arg)
    | ESelect (SV x) _ => [x]
    | EUpdate (SV x) _ rhs => x :: (freeVars rhs)
    | EUpdate (DV _) _ rhs => freeVars rhs
    | ELet x e body =>
      (freeVars e) ++
      (List.remove id_eq_dec x (freeVars body))
    | EPar e1 e2 e3 => (freeVars e1) ++ (freeVars e2) ++ (freeVars e3)
    | ECast t e => freeVars e
    | ELock (SV x) _ e => x :: (freeVars e)
    | ELock (DV _) _ e => freeVars e
    | ELocked _ e => freeVars e
    | _ => nil
  end.

Definition subst_var (x : svar) (y : dvar) (z : var) : var :=
  match z with
    | (SV z) => if id_eq_dec x z then DV y else SV z
    | (DV z) => (DV z)
  end.

Hint Unfold subst_var.

Fixpoint subst (x : svar) (y : dvar) (e : expr) : expr :=
  match e with
    | EVar z => EVar (subst_var x y z)
    | ELet z e' body =>
        ELet z (subst x y e')
             (if id_eq_dec x z then
                body
              else
                (subst x y body))
    | ECall z m arg =>
        ECall (subst_var x y z)
              m (subst x y arg)
    | ESelect z f => ESelect (subst_var x y z) f
    | EUpdate z f rhs =>
        EUpdate (subst_var x y z)
                f (subst x y rhs)
    | EPar e1 e2 e3 =>
        EPar (subst x y e1)
             (subst x y e2)
             (subst x y e3)
    | ECast t e =>
        ECast t (subst x y e)
    | ELock z r e =>
        ELock (subst_var x y z) r (subst x y e)
    | ELocked L e =>
        ELocked L (subst x y e)
    | _ => e
  end.

Fixpoint locks (e : expr) : list lock :=
  match e with
    | ECall _ _ arg => locks arg
    | EUpdate _ _ rhs => locks rhs
    | ELet _ e body => locks e ++ locks body
    | ECast _ e => locks e
    | EPar e1 e2 e3 => locks e1 ++ locks e2 ++ locks e3
    | ELock _ _ e => locks e
    | ELocked L e => L :: locks e
    | _ => nil
  end.

Definition no_locks (e : expr) : Prop :=
  locks e = nil.

(*
==============
Configuration
==============
*)

(*
------
Stack
------
*)

Definition dvar_map := partial_map dvar val.

(*
------
Locks
------
*)

Inductive lock_status : Type :=
  | LLocked : lock_status
  | LUnlocked : lock_status.

Definition region_locks := partial_map region_id lock_status.

(*
-----
Heap
-----
*)

Definition dyn_fields := partial_map field_id val.

Definition object := (class_id * dyn_fields * region_locks)%type.

Definition heap := list object.

Definition heapExtend (H : heap) (obj : object) := snoc H obj.

Definition heapLookup (H : heap) (l : loc) :=
  nth_error H l.

Fixpoint heapUpdate (H : heap) (l : loc) (obj : object) :=
  match H with
  | nil => nil
  | obj' :: H' =>
    match l with
    | O    => obj :: H'
    | S l' => obj' :: (heapUpdate H' l' obj)
    end
  end.

(*
--------
Threads
--------
*)

Inductive threads :=
  | T_EXN    : list lock -> threads
  | T_Thread : list lock -> expr -> threads
  | T_Async  : threads -> threads -> expr -> threads.

Definition threads_done (thr : threads) :=
  match thr with
    | T_Thread _ (EVal _) => True
    | _ => False
  end.

Definition threads_exn (thr : threads) :=
  match thr with
    | T_EXN _ => True
    | _ => False
  end.

Fixpoint heldLocks (T : threads) :=
  match T with
    | T_EXN Ls => Ls
    | T_Thread Ls _ => Ls
    | T_Async T1 T2 _ => heldLocks T1 ++ heldLocks T2
  end.

Fixpoint leftmost_locks (T : threads) : list lock :=
  match T with
    | T_EXN Ls => Ls
    | T_Thread Ls _ => Ls
    | T_Async T1 _ _ => leftmost_locks T1
  end.

Fixpoint t_locks (T : threads) :=
  match T with
    | T_EXN _ => nil
    | T_Thread _ e => locks e
    | T_Async T1 T2 e => t_locks T1 ++ t_locks T2 ++ locks e
  end.

(*
--------------
Configuration
--------------
*)

Definition configuration := (heap * dvar_map * nat * threads)%type.

Definition cfg_done (cfg : configuration) : Prop :=
  match cfg with
    | (_, _, _, thr) => threads_done thr
  end.

Definition cfg_exn (cfg : configuration) : Prop :=
  match cfg with
    | (_, _, _, thr) => threads_exn thr
  end.

(*
========
Program
========
*)

Inductive fieldDecl : Type :=
  | Field : field_id -> ty -> region_id -> fieldDecl.

Inductive methodDecl : Type :=
  | Method : method_id -> (svar * ty) -> ty -> expr -> methodDecl.

Inductive classDecl : Type :=
  | Cls : class_id -> interface_id -> list fieldDecl -> list methodDecl -> classDecl.

Inductive methodSig : Type :=
  | MethodSig : method_id -> (svar * ty) -> ty -> methodSig.

Inductive interfaceDecl : Type :=
  | Interface : interface_id -> list methodSig -> interfaceDecl
  | ExtInterface : interface_id -> interface_id -> interface_id -> interfaceDecl.

Definition program := (list classDecl * list interfaceDecl * expr)%type.

Definition classLookup(P : program)(c : class_id) : option classDecl :=
  match P with
    | (cs, _, _) =>
      let c_eq c cls := match cls with
                          | Cls c' _ _ _ => beq_nat c c'
                        end
      in
      find (c_eq c) cs
  end.

Definition interfaceLookup(P : program)(i : interface_id) : option interfaceDecl :=
  match P with
    | (_, ids, _) =>
      let i_eq i intr := match intr with
                          | Interface i' _ => beq_nat i i'
                          | ExtInterface i' _ _ => beq_nat i i'
                        end
      in
      find (i_eq i) ids
  end.

Definition fieldLookup(fs : list fieldDecl)(f : field_id) :=
  let f_eq f fld := match fld with
                     | Field f' _ _ => beq_nat f f'
                    end
  in
  find (f_eq f) fs.

Definition fields(P : program)(t : ty) :=
  match t with
    | TClass c => match classLookup P c with
                    | Some (Cls _ _ fs _) => Some fs
                    | None => None
                  end
    | _ => None
  end.

Definition methodLookup(ms : list methodDecl)(m : method_id) :=
  let m_eq m mtd := match mtd with
                      | Method m' _ _ _ => beq_nat m m'
                    end
  in
  find (m_eq m) ms.

Definition methods(P : program)(t : ty) :=
  match t with
    | TClass c => match classLookup P c with
                    | Some (Cls _ _ _ ms) => Some ms
                    | None => None
                  end
    | _ => None
  end.

Definition methodSigLookup(ms : list methodSig)(m : method_id) :=
  let m_eq m mtd := match mtd with
                      | MethodSig m' _ _ => beq_nat m m'
                    end
  in
  find (m_eq m) ms.

Definition extractSigs(ms : list methodDecl) :=
  let extract := fun mtd => match mtd with
                              | Method m param t e => MethodSig m param t
                            end
  in
  map extract ms.

Inductive methodSigs(P : program) : ty -> list methodSig -> Prop :=
  | MSigs_Class :
      forall c i fs ms,
        classLookup P c = Some (Cls c i fs ms) ->
        methodSigs P (TClass c) (extractSigs ms)
  | MSigs_Interface :
      forall i msigs,
        interfaceLookup P i = Some (Interface i msigs) ->
        methodSigs P (TInterface i) msigs
  | MSigs_ExtInterface :
      forall i i1 i2 msigs1 msigs2,
        interfaceLookup P i = Some (ExtInterface i i1 i2) ->
        methodSigs P (TInterface i1) msigs1 ->
        methodSigs P (TInterface i2) msigs2 ->
        methodSigs P (TInterface i) (msigs1 ++ msigs2)
  | MSigs_Unit :
      methodSigs P TUnit [].


Fixpoint declsToFields (l : list fieldDecl) :=
  match l with
    | nil => empty
    | fd :: fs =>
      match fd with
        | Field f _ _ =>
          extend (declsToFields fs) f VNull
      end
  end.

Inductive declsToRegionLocks (fs : list fieldDecl) : region_locks -> Prop :=
  | DeclsToRegionLocks :
      forall RL,
        (forall f t r, fieldLookup fs f = Some (Field f t r) ->
                       RL r = Some LUnlocked) ->
        declsToRegionLocks fs RL.