type className = string
type interfaceName = string
type varName = string
type fieldName = string
type methodName = string
type location = int

(** OOlong types: class types, interface types, the unit type and
   the int type. Reference types are unresolved before they are
   categorised as class or interface types (i.e. before
   typechecking). *)
type typ =
  | UnresolvedType of string
  | ClassType of className
  | InterfaceType of interfaceName
  | UnitType
  | IntType

let showType = function
  | UnresolvedType s -> "<" ^ s ^ ">"
  | ClassType c -> c
  | InterfaceType i -> i
  | UnitType -> "Unit"
  | IntType -> "int"

(** OOlong expressions: null, variables, field reads and updates,
   method calls, let expressions, object creation, upcasts,
   concurrency, and synchronisation via locks. During evaluation,
   expressions can also denote a held lock and the value of a
   reference. *)
type expr =
  | Null
  | Var of varName
  | Int of int
  | Add of expr * expr
  | FieldAccess of varName * fieldName
  | FieldUpdate of varName * fieldName * expr
  | MethodCall of varName * methodName * expr
  | Let of varName * expr * expr
  | New of className
  | Cast of typ * expr
  | FinishAsync of expr * expr * expr
  | Lock of varName * expr
  (* Dynamic expressions *)
  | Locked of location * expr
  | Loc of location

(** [isVal e] returns true if [e] is a value, and false otherwise. *)
let isVal = function
  | Null | Loc _ | Int _ -> true
  | _ -> false

let rec showExpr = function
  | Null -> "null"
  | Loc l -> string_of_int l
  | Var x -> x
  | Int n -> string_of_int n
  | Add (e1, e2) -> showExpr e1^" + "^showExpr e2
  | FieldAccess (x, f) -> x ^ "." ^ f
  | FieldUpdate (x, f, e) -> x ^ "." ^ f ^ " = " ^ showExpr e
  | MethodCall (x, m, e) -> x ^ "." ^ m ^ "(" ^ showExpr e ^ ")"
  | Let (x, e, body) -> "let " ^ x ^ " = " ^ showExpr e ^ " in " ^ showExpr body
  | New c -> "new " ^ c
  | Cast (t, e) -> "(" ^ showType t ^ ") " ^ showExpr e
  | FinishAsync (e1, e2, e3) ->
     "finish{ async {" ^ showExpr e1 ^
       "} async { " ^ showExpr e2 ^ "}}; " ^ showExpr e3
  | Lock (x, e) -> "lock " ^ x ^ " in " ^ showExpr e
  | Locked (l, e) -> "locked(" ^ string_of_int l ^ "){ " ^ showExpr e ^ "}"

let substVar x x' y = if x = x' then y else x'

(** [subst x y e] replaces all occurrences of [x] in [e] with [y]. *)
let rec subst x y = function
  | Null
    | Loc _
    | Int _
    | New _ as e -> e
  | Var x' -> Var (substVar x x' y)
  | Add (e1, e2) -> Add (subst x y e1, subst x y e2)
  | FieldAccess (x', f) -> FieldAccess (substVar x x' y, f)
  | FieldUpdate (x', f, e) -> FieldUpdate (substVar x x' y, f, subst x y e)
  | MethodCall (x', m, e) -> MethodCall (substVar x x' y, m, subst x y e)
  | Let (x', e, body) ->
     if x = x' then
       Let (x', subst x y e, body)
     else
       Let (x', subst x y e, subst x y body)
  | Cast (t, e) -> Cast (t, subst x y e)
  | FinishAsync (e1, e2, e3) ->
     FinishAsync (subst x y e1, subst x y e2, subst x y e3)
  | Lock (x', e) -> Lock (substVar x x' y, subst x y e)
  | Locked (l, e) -> Locked (l, subst x y e)

(** [freeVars e] returns a list of all free variables in [e]. *)
let freeVars e =
  let rec freeVars' = function
    | Null
      | Loc _
      | Int _
      | New _ -> []
    | Var x
      | FieldAccess (x, _) -> [x]
    | Add (e1, e2) -> freeVars' e1 @ freeVars' e2
    | FieldUpdate (x, _, e)
      | MethodCall (x, _, e)
      | Lock (x, e) -> x :: freeVars' e
    | Let (x, e, body) ->
       freeVars' e @ List.filter (fun x' -> x != x') (freeVars' body)
    | Cast (_, e)
      | Locked (_, e) -> freeVars' e
    | FinishAsync (e1, e2, e3) ->
       freeVars' e1 @ freeVars' e2 @ freeVars' e3
  in
  List.sort_uniq compare (freeVars' e)

(** Field definitions have a name and a type. *)
type fieldDef =
  | FieldDef of fieldName * typ

let showFieldDef (FieldDef (f, t)) = f ^ " : " ^ showType t

(** Method signatures have a name, a typed argument and a return type. *)
type methodSig =
  | MethodSig of methodName * varName * typ * typ

let showMethodSig (MethodSig(m, x, t1, t2)) =
  m ^ "(" ^ x ^ " : " ^ showType t1 ^ ") : " ^ showType t2

(** Method definitions have a signature and a method body. *)
type methodDef =
  | MethodDef of methodSig * expr

let showMethodDef (MethodDef(msig, e)) =
  "def " ^ showMethodSig msig ^ " { " ^ showExpr e ^ " } "

(** A class has a name, implements an interface, and provides a
   number of fields and methods. *)
type classDef =
  | ClassDef of className * interfaceName * fieldDef list * methodDef list

let getClassName = function ClassDef (c, _, _, _) -> c

(** [intercalate s l] returns the concatenation of all strings in
   [l], with [s] interspersed between each string (this is used
   for printing). *)
let rec intercalate s = function
  | [] -> ""
  | [x] -> x
  | x::xs -> x ^ s ^ intercalate s xs

(** [showClassDef c] returns a string representation of c. *)
let showClassDef (ClassDef(c, i, flds, mtds)) =
  let fields = intercalate " " (List.map (fun f -> showFieldDef f) flds) in
  let methods = intercalate " " (List.map (fun f -> showMethodDef f) mtds) in
  "class " ^ c ^ " implements " ^ i ^ " {" ^ fields ^ " " ^ methods ^ "}"

(** An interface is either a "leaf interface" which provides a
   list of method signatures, or a "branch interface" which joins
   together two other interfaces. *)
type interfaceDef =
  | InterfaceDef of interfaceName * methodSig list
  | ExtInterfaceDef of interfaceName * interfaceName * interfaceName

let getInterfaceName = function
  | InterfaceDef (i, _)
    | ExtInterfaceDef (i, _, _) -> i

let showInterfaceDef = function
  | InterfaceDef(i, msigs) ->
     let signatures =
       intercalate " " (List.map (fun m -> showMethodSig m) msigs)
     in
     "interface " ^ i ^ " {" ^ signatures ^ "}"
  | ExtInterfaceDef(i, i1, i2) ->
     "interface " ^ i ^ " extends " ^ i1 ^ ", " ^ i2

(** An OOlong program consists of a list of interface and class
   definitions and an expression which is run with these
   definitions in scope. *)
type program =
  | Program of interfaceDef list * classDef list * expr

let showProgram (Program(idefs, cdefs, e)) =
  let interfaces =
    intercalate " " (List.map (fun i -> showInterfaceDef i) idefs)
  in
  let classes =
    intercalate " " (List.map (fun c -> showClassDef c) cdefs)
  in
  interfaces ^ classes ^ " " ^ showExpr e
(* TODO: Proper pretty-printing *)
