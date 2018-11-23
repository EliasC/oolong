open Ast
open Tables

module Env = struct
  open Ast
  open Tables

  module VarTable = Map.Make(String)
  type varTable = typ VarTable.t

  (** The environment needed to typecheck a program, containing
  classes and interfaces, as well as a map from variable names to
  types. *)
  type environment =
    | Env of interfaceTable * classTable * varTable

  (** Return an environment with the classes, interfaces and
  variables defined by [cTable], [iTable] and [vars] *)
  let newEnv iTable cTable vars = Env (iTable, cTable, vars)

  (** Return an extended version of the environment [env] with the
  mapping [x : t] added *)
  let extendEnv env x t = match env with
    | Env (ctable, itable, vars) ->
       Env (ctable, itable, VarTable.add x t vars)
end

open Env
open Tables
exception TCError of string

(** [lookupClass env c] finds the class definition named [c] in
  the program defined by [env]. Raises [TCError] if the class is
  not defined. *)
let lookupClass env c = match env with
  | Env (_, ctable, _) ->
     match ClassTable.lookup c ctable with
     | Some def -> def
     | None -> raise (TCError ("Unknown class: " ^ c))

(** [lookupInterface env i] finds the interface definition named
  [i] in the program defined by [env]. Raises [TCError] if the
  interface is not defined. *)
let lookupInterface env i = match env with
  | Env (itable, _, _) ->
     match InterfaceTable.lookup i itable with
     | Some def -> def
     | None -> raise (TCError ("Unknown interface: " ^ i))

(** [resolveType env t] checks the well-formedness of the type
  [t] in the program defined by the environment [env] and resolves
  it if need be. Raises [TCError] if the type is not
  well-formed. *)
let rec resolveType env t = match t with
  | UnresolvedType "Unit" -> UnitType
  | UnresolvedType "int" -> IntType
  | UnresolvedType s ->
     (try resolveType env (ClassType s) with
      | TCError _ ->
         try resolveType env (InterfaceType s) with
         | TCError _ -> raise (TCError ("Unknown type: " ^ s)))
  | ClassType c -> let _ = lookupClass env c in t
  | InterfaceType i -> let _ = lookupInterface env i in t
  | _ -> t

let resolveMethodSig env (MethodSig(m, x, tx, te)) =
  MethodSig(m, x, resolveType env tx, resolveType env te)

(** [lookupVar env x] finds the type of variable [x] in the
  current environment [env]. Raises [TCError] if the variable is
  not defined. *)
let lookupVar env x = match env with
  | Env (_, _, vars) ->
     match VarTable.find_opt x vars with
     | Some t -> t
     | None -> raise (TCError ("Unknown variable: " ^ x))

(** [lookupField env t f] finds the type of field [f] in type
  [t] given the program defined by [env]. Raises [TCError] if the
  field is not found, or if [t] is not a class type. *)
let lookupField env t f =
  match t with
  | ClassType c ->
     (let fEq = function FieldDef (f', _) -> f = f' in
      match lookupClass env c with
      | ClassDef (_, _, fields, _) ->
         match List.find_opt fEq fields with
         | Some (FieldDef (_, t')) -> resolveType env t'
         | None -> raise (TCError ("Unknown field in class '" ^ c ^ "': " ^ f))
     )
  | _ -> raise (TCError ("Cannot look up field in non-class: " ^ showType t))

(** [collectMethodSigs env idef] collects the signatures of all
  methods reachable from the interface definition [idef], given
  the program defined by [env]. *)
let rec collectMethodSigs env = function
  | InterfaceDef (_, mSigs) -> mSigs
  | ExtInterfaceDef (_, i1, i2) ->
     collectMethodSigs env (lookupInterface env i1) @
       collectMethodSigs env (lookupInterface env i2)

(** [lookupMethodSig env t m] finds the signature of method [m]
  in type [t] given the program defined by [env]. Raises a
  [TCError] if the method is not found, or if [t] is not a class
  or interface type. *)
let lookupMethodSig env t m =
  let mSigEq = function MethodSig (m', _, _, _) -> m = m' in
  let mEq = function MethodDef (mSig, _) -> mSigEq mSig in
  match t with
  | ClassType c ->
     (match lookupClass env c with
      | ClassDef (_, _, _, methods) ->
         match List.find_opt mEq methods with
         | Some MethodDef (mSig, _) -> resolveMethodSig env mSig
         | None -> raise (TCError ("Unknown method in class '" ^ c ^
                                     "': " ^ m))
     )
  | InterfaceType i ->
     let mSigs = collectMethodSigs env (lookupInterface env i) in
     (match List.find_opt mSigEq mSigs with
      | Some mSig -> resolveMethodSig env mSig
      | None -> raise (TCError ("Unknown method in interface '" ^ i ^
                                  "': " ^ m)))

  | _ -> raise (TCError ("Cannot look up method in type: " ^ showType t))

(** [isSubtypeOf env sub super] checks if [sub] is a subtype of
  [super] in the program defined by [env] and returns true or
  false. *)
let rec isSubtypeOf env sub super =
  match sub, super with
  | ClassType c, InterfaceType i ->
     let ClassDef (_, i', _, _) = lookupClass env c in
     isSubtypeOf env (InterfaceType i') super
  | InterfaceType i, InterfaceType i' ->
     (match lookupInterface env i with
      | InterfaceDef _ -> i = i'
      | ExtInterfaceDef (_, i1, i2) ->
         i = i' ||
           isSubtypeOf env (InterfaceType i1) super ||
             isSubtypeOf env (InterfaceType i2) super
     )
  | _ -> sub = super

(** [assertSubtypeOf env sub super] raises a [TCError] if [sub]
  is not a subtype of [super] in the program defined by [env]. *)
let assertSubtypeOf env sub super =
  if not (isSubtypeOf env sub super) then
    raise (TCError ("Type '" ^ showType sub ^
                      "' is not a subtype of '" ^ showType super ^ "'"))

(** [inferType env e] typechecks the expression [e] in the
   environment [env] and returns its type if it can be inferred.
   Raises [TCError] if the expression is not well-formed or if the
   type cannot be inferred. *)
let rec inferType env = function
  | Var x -> lookupVar env x
  | Int n -> IntType
  | Add (e1, e2) ->
     let _ = checkType env e1 IntType in
     checkType env e2 IntType
  | FieldAccess (x, f) ->
     let c = inferType env (Var x) in
     lookupField env c f
  | FieldUpdate (x, f, e) ->
     let c = inferType env (Var x) in
     let t = lookupField env c f in
     let _ = checkType env e t in
     UnitType
  | MethodCall (x, m, e) ->
     let targetType = inferType env (Var x) in
     let MethodSig (_, _, expectedType, resultType) =
       lookupMethodSig env targetType m in
     let _ = checkType env e expectedType in
     resultType
  | Let (x, e, body) ->
     let t = inferType env e in
     inferType (extendEnv env x t) body
  | New c ->
     let t = resolveType env (UnresolvedType c) in
     (match t with
      | ClassType _ -> t
      | _ ->
         raise (TCError ("Cannot create instance of type: " ^ showType t)))
  | Cast (t, e) -> checkType env e (resolveType env t)
  | FinishAsync (e1, e2, e3) ->
     let _ = inferType env e1 in
     let _ = inferType env e2 in
     let vars1 = freeVars e1 in
     let vars2 = freeVars e2 in
     (match List.filter (fun x -> List.mem x vars2) vars1 with
      | x :: _ ->
         raise (TCError ("Variable appears in both branches of a fork: " ^ x))
      | [] -> inferType env e3)
  | Lock (x, e) ->
     let _ = inferType env (Var x) in
     inferType env e
  | Loc _ | Locked _ ->
     raise (TCError "Dynamic constructs cannot be statically typechecked")
  | _ -> raise (TCError "Cannot infer type. Try adding type annotations to null")

(** [checkType env e t] checks if [e] has type [t] in environment
   [env], and otherwise raises [TCError]. *)
and checkType env e expected =
  match e with
  | Null when expected = IntType -> raise (TCError "Integers cannot be null")
  | Null -> expected
  | _ ->
     let t = inferType env e in
     assertSubtypeOf env t expected; expected

(** [tcField env f] typechecks the field [f] in environment [env]. *)
let tcField env (FieldDef (f, t)) = FieldDef (f, resolveType env t)

(** [tcMethod env m] typechecks the method [m] in environment [env]. *)
let tcMethod env (MethodDef (MethodSig (m, x, tx, te), e)) =
  let tx' = resolveType env tx in
  let te' = resolveType env te in
  let _ = checkType (extendEnv env x tx') e te' in
  MethodDef (MethodSig (m, x, tx', te'), e)

(** [tcClass env c] typechecks the class definition [c] in
   environment [env]. *)
let tcClass env (ClassDef (c, i, fields, methods)) =
  let _ = resolveType env (InterfaceType i) in
  let env' = extendEnv env "this" (ClassType c) in
  let fields' = List.map (tcField env') fields in
  let methods' = List.map (tcMethod env') methods in
  let mSigs = collectMethodSigs env (lookupInterface env i) in
  let mSigEq (MethodSig (m1, _, t11, t12)) (MethodSig (m2, _, t21, t22)) =
    m1 = m2 && t11 = t21 && t12 = t22
  in
  let matchesSig msig (MethodDef (msig', _)) = mSigEq msig msig' in
  if not (List.for_all (fun mSig -> List.exists (matchesSig mSig) methods) mSigs)
  then raise (TCError "Class does not implement its declared interface");
  ClassDef (c, i, fields', methods')
  (* TODO: Check for duplicates *)

(** [tcMethodSig env msig] typechecks the method signature [msig]
   in environment [env]. *)
let tcMethodSig env (MethodSig (m, x, t1, t2)) =
  let t1' = resolveType env t1 in
  let t2' = resolveType env t2 in
  MethodSig (m, x, t1', t2')

(** [tcInterface env i] typechecks the interface definition [i] in
   environment [env]. *)
let tcInterface env def =
  let rec tcInterface' env seen = function
    | InterfaceDef (i, msigs) ->
       if List.mem i seen then
         raise (TCError ("Interface inherits itself: " ^ i));
       let msigs' = List.map (tcMethodSig env) msigs in
       InterfaceDef (i, msigs')
    | ExtInterfaceDef (i, i1, i2) ->
       if List.mem i seen then
         raise (TCError ("Interface inherits itself: " ^ i));
       let def1 = lookupInterface env i1 in
       let def2 = lookupInterface env i2 in
       let _ = tcInterface' env (i::seen) def1 in
       tcInterface' env (i::seen) def2
  in
  tcInterface' env [] def

(** [tcInterface env p] typechecks the program [p] in environment
   [env] and returns its type. *)
let tcProgram env (Program (interfaces, classes, e)) =
  let interfaces' = List.map (tcInterface env) interfaces in
  let classes' = List.map (tcClass env) classes in
  let _ = inferType env e in
  Program (interfaces', classes', e)
  (* TODO: Check for duplicates *)

(** [typecheck p] typechecks the program p, and returns its type.
   Raises [TCError] if the program is not well formed. *)
let typecheck (Program (interfaces, classes, e) as p) =
  let iTable = InterfaceTable.build interfaces in
  let cTable = ClassTable.build classes in
  let env = newEnv iTable cTable VarTable.empty in
  tcProgram env p
