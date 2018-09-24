open Ast
open Tables

exception EvaluationException of string

type value =
  | VNull
  | VLoc of location

let toValue = function
  | Null -> VNull
  | Loc l -> VLoc l
  | e -> raise (EvaluationException ("Not a value: " ^ showExpr e))

let fromValue = function
  | VNull -> Null
  | VLoc l -> Loc l

let showValue = function
  | VNull -> "null"
  | VLoc l -> string_of_int l

let lookupMethod ctable c m =
  match lookupClass ctable c with
  | None -> raise (EvaluationException ("No such class: " ^ c))
  | Some (ClassDef(_, _, _, methods)) ->
    let mEq = function MethodDef (MethodSig(m', _, _, _), _) -> m = m' in
     match List.find_opt mEq methods with
     | Some m -> m
     | None ->
        raise (EvaluationException ("No such method in class '" ^ c ^ "': " ^ m))

module Object = struct
  module FieldMap = Map.Make(String)
  type fieldMap = value FieldMap.t

  let rec buildFieldMap = function
    | [] -> FieldMap.empty
    | FieldDef(f, _)::fs -> FieldMap.add f VNull (buildFieldMap fs)

  let showFieldMap fs =
    let showMapping f v = Printf.sprintf "%s -> %s" f (showValue v) in
    let s = ref "" in
    let set f v = if !s = "" then
                    s := showMapping f v
                  else
                    s := !s ^ ", " ^ showMapping f v
    in
    FieldMap.iter set fs; "{" ^ !s ^ "}"

  type lock =
    | Locked
    | Unlocked

  let showLock = function
    | Locked -> "Locked"
    | Unlocked -> "Unlocked"

  type t = className * fieldMap * lock

  let make c fs = (c, buildFieldMap fs, Unlocked)

  let show (c, fs, l) =
    Printf.sprintf "(%s, %s, %s)" c (showFieldMap fs) (showLock l)

  let getClass (c, _, _) : className = c
  let lookupField f (_, fs, _) = FieldMap.find f fs
  let updateField f v (c, fs, l) = (c, FieldMap.add f v fs, l)
  let lock (c, fs, _) = (c, fs, Locked)
  let unlock (c, fs, _) = (c, fs, Unlocked)
  let isLocked (_, _, l) = l = Locked
end

module Heap = struct
  type t = (Object.t array) ref

  let empty : t = ref [||]

  let show heap =
    let showMapping i obj = Printf.sprintf "%d -> %s" i (Object.show obj) in
    let s = ref "" in
    let set i obj = s := !s ^ "\n " ^ showMapping i obj in
    Array.iteri set !heap; "{" ^ !s ^ "\n}"

  let alloc heap c fields =
    let index = Array.length !heap in
    heap := Array.append !heap [|Object.make c fields|];
    index
  let lookup heap i = !heap.(i)
  let update heap i f = !heap.(i) <- f !heap.(i)
end

module Vars = struct
  module VarMap = Map.Make(String)
  type varMap = value VarMap.t
  type t = (varMap * int) ref

  let empty : t = ref (VarMap.empty, 0)

  let show vars =
    let (map, _) = !vars in
    let showMapping x v = Printf.sprintf "%s -> %s" x (showValue v) in
    let s = ref "" in
    let set x v = s := !s ^ "\n " ^ showMapping x v in
    VarMap.iter set map; "{" ^ !s ^ "\n}"

  let lookup vars x = let (map, _) = !vars in VarMap.find x map
  let update vars x v =
    let (map, n) = !vars in
    vars := (VarMap.add x v map, n)
  let fresh vars x =
    let (map, n) = !vars in
    if VarMap.mem x map then
      let x' = x ^ "#" ^ string_of_int n in
      vars := (map, succ n); x'
    else
      x
end

module Threads = struct
  type threads =
    | Thread of location list * expr
    | ForkJoin of threads * threads * expr
    | NullPointerException of expr

  let make e = Thread([], e)
  let fork t e1 e2 = ForkJoin (t, make e1, e2)
  let isDone = function
    | Thread (_, e) -> isVal e
    | NullPointerException _ -> true
    | _ -> false
  let rec showThreads = function
    | Thread (locks, e) -> "([], " ^ showExpr e ^ ")"
    | ForkJoin (t1, t2, e) ->
       "(" ^ showThreads t1 ^ " || " ^ showThreads t2 ^
       " |> " ^ showExpr e ^ ")"
    | NullPointerException e -> "<NullPointerException: " ^ showExpr e ^ ">"
end

open Threads
type obj = Object.t
type heap = Heap.t
type vars = Vars.t

type cfg = heap * vars * threads

module Context = struct
  exception ContextException of string
  let rec extract = function
    | Null
      | Loc _ -> raise (ContextException "Cannot extract a value")
    (* These expressions can be evaluated directly *)
    | Var _
      | FieldAccess _
      | New _
      | Lock _
      | FinishAsync _ as e -> e
    (* These expressions can be evaluated when subexpressions are values *)
    | FieldUpdate (_, _, e')
      | MethodCall (_, _, e')
      | Let (_, e', _)
      | Cast (_, e')
      | Locked (_, e') as e when isVal(e') -> e
    (* Evaluate subexpression first *)
    | FieldUpdate (_, _, e')
      | MethodCall (_, _, e')
      | Let (_, e', _)
      | Cast (_, e')
      | Locked (_, e') -> extract e'

  let rec insert v = function
    | Null
      | Loc _ -> raise (ContextException "Cannot insert into a value")
    (* These expressions can be replaced directly *)
    | Var _
      | FieldAccess _
      | New _
      | Lock _
      | FinishAsync _ -> v
    (* These expressions can be replaced when subexpressions are values *)
    | FieldUpdate (_, _, e')
      | MethodCall (_, _, e')
      | Let (_, e', _)
      | Cast (_, e')
      | Locked (_, e') when isVal(e') -> v
    (* Insert value in subexpressions *)
    | FieldUpdate (x, f, e') -> FieldUpdate (x, f, insert v e')
    | MethodCall (x, m, e') -> MethodCall (x, m, insert v e')
    | Let (x, e', body) -> Let (x, insert v e', body)
    | Cast (l, e') -> Cast (l, insert v e')
    | Locked (l, e') -> Locked (l, insert v e')
end

exception BlockedException

let reduce
      (ctable : classTable)
      (heap : Heap.t) (vars : Vars.t) locks = function
  | Null
    | Loc _ -> raise (EvaluationException "Cannot reduce a value")
  | Var x -> Thread (locks, fromValue (Vars.lookup vars x))
  | FieldAccess (x, f) as e ->
     (match Vars.lookup vars x with
      | VNull -> NullPointerException e
      | VLoc l ->
         let obj = Heap.lookup heap l in
         Thread (locks, fromValue (Object.lookupField f obj))
     )
  | FieldUpdate (x, f, v) as e ->
     (match Vars.lookup vars x with
      | VNull -> NullPointerException e
      | VLoc l ->
         Heap.update heap l (Object.updateField f (toValue v));
         Thread (locks, Null)
     )
  | MethodCall (x, m, v) as e ->
     (match Vars.lookup vars x with
      | VNull -> NullPointerException e
      | VLoc l ->
         let obj = Heap.lookup heap l in
         let c = Object.getClass obj in
         let MethodDef(MethodSig(_, y, t, _), body) = lookupMethod ctable c m in
         let y' = Vars.fresh vars y in
         let this' = Vars.fresh vars "this" in
         Vars.update vars y' (toValue v);
         Vars.update vars this' (VLoc l);
         let body' = subst y y' (subst "this" this' body) in
         Thread (locks, body')
     )
  | Let (x, v, body) ->
     let x' = Vars.fresh vars x in
     Vars.update vars x' (toValue v);
     Thread (locks, subst x x' body)
  | New c ->
     let ClassDef(_, _, fields, _) = ClassTable.find c ctable in
     let l = Heap.alloc heap c fields in
     Thread (locks, Loc l)
  | Cast (_, v) -> Thread (locks, v)
  | Lock (x, body) as e ->
     (match Vars.lookup vars x with
      | VNull -> NullPointerException e
      | VLoc l ->
         let obj = Heap.lookup heap l in
         if Object.isLocked obj then
           if List.mem l locks then
             (* Reentrant case *)
             Thread (locks, body)
           else
             raise BlockedException
         else
           (Heap.update heap l Object.lock;
            Thread (l :: locks, Locked (l, body)))
     )
  | Locked (l, v) ->
     Heap.update heap l Object.unlock;
     Thread (List.filter (fun l' -> l != l') locks, v)
  | FinishAsync (e1, e2, e3) ->
     Threads.fork (Thread(locks, e1)) e2 e3

let rec reduceThreads ctable heap vars scheduler = function
  | Thread (locks, e) ->
     let sub = Context.extract e in
     (match reduce ctable heap vars locks sub with
      | Thread (locks', sub') ->
         let e' = Context.insert sub' e in
         Thread (locks', e')
      | ForkJoin (t1, t2, sub') ->
         let e' = Context.insert sub' e in
         ForkJoin (t1, t2, e')
      | NullPointerException e -> NullPointerException e)
  | ForkJoin (NullPointerException e, _, _) ->
     NullPointerException e
  | ForkJoin (_, NullPointerException e, _) ->
     NullPointerException e
  | ForkJoin (Thread(locks, v) as t1, t2, e) when isDone t1 ->
     if isDone(t2) then
       Thread (locks, e)
     else
       let t2' = reduceThreads ctable heap vars scheduler t2 in
       ForkJoin (t1, t2', e)
  | ForkJoin (t1, (Thread(locks, v) as t2), e) when isDone t2 ->
     let t1' = reduceThreads ctable heap vars scheduler t1 in
     ForkJoin (t1', t2, e)
  | ForkJoin (t1, t2, e) ->
     if scheduler () then
       tryFirstThread ctable heap vars scheduler t1 t2 e
     else
       trySecondThread ctable heap vars scheduler t1 t2 e
  | NullPointerException e ->
     raise (EvaluationException "Tried to reduce an exception ")

and tryFirstThread ctable heap vars scheduler t1 t2 e =
  try
    let t1' = reduceThreads ctable heap vars scheduler t1 in
    ForkJoin (t1', t2, e)
  with
  | BlockedException ->
     let t2' = reduceThreads ctable heap vars scheduler t2 in
     ForkJoin (t1, t2', e)
and trySecondThread ctable heap vars scheduler t1 t2 e =
  try
    let t2' = reduceThreads ctable heap vars scheduler t2 in
    ForkJoin (t1, t2', e)
  with
  | BlockedException ->
     let t1' = reduceThreads ctable heap vars scheduler t1 in
     ForkJoin (t1', t2, e)

type result =
  | Done of cfg * int
  | Blocked of cfg * int

let rec evalLoop
          (debug : bool)
          (ctable : classTable)
          (heap : Heap.t) (vars : Vars.t) (threads : threads)
          (scheduler : unit -> bool)
          (steps : int) =
  if isDone threads then
    Done ((heap, vars, threads), steps)
  else
    try
      let threads' = reduceThreads ctable heap vars scheduler threads in
      if debug then print_string (showThreads threads' ^ "\n");
      evalLoop debug ctable heap vars threads' scheduler (steps + 1)
    with
    | BlockedException -> Blocked ((heap, vars, threads), steps)

let interpret (Program(_, classes, e)) scheduler debug =
  let ctable = Tables.buildClassTable classes in
  let heap = Heap.empty in
  let vars = Vars.empty in
  let thread = Threads.make e in
  evalLoop debug ctable heap vars thread scheduler 0
