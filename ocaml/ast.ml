type className = string
module ClassNameCmp : Set.OrderedType =
  struct type t = className let compare = compare end

type interfaceName = string
module InterfaceNameCmp : Set.OrderedType =
  struct type t = interfaceName let compare = compare end

type typ =
  | UnresolvedType of string
  | ClassType of className
  | InterfaceType of interfaceName
  | UnitType
  | NullType

let showType = function
  | UnresolvedType s -> "<" ^ s ^ ">"
  | ClassType c -> c
  | InterfaceType i -> i
  | UnitType -> "Unit"
  | NullType -> "Null type"

type varName = string
module VarNameCmp : Set.OrderedType =
  struct type t = varName let compare = compare end

type fieldName = string
module FieldNameCmp : Set.OrderedType =
  struct type t = fieldName let compare = compare end

type methodName = string
module MethodNameCmp : Set.OrderedType =
  struct type t = methodName let compare = compare end

type location = int

type expr =
  | Null
  | Loc of location
  | Var of varName
  | FieldAccess of varName * fieldName
  | FieldUpdate of varName * fieldName * expr
  | MethodCall of varName * methodName * expr
  | Let of varName * expr * expr
  | New of className
  | Cast of typ * expr
  | FinishAsync of expr * expr * expr
  | Lock of varName * expr
  | Locked of location * expr

let isVal = function
  | Null | Loc _ -> true
  | _ -> false

let rec showExpr = function
  | Null -> "null"
  | Loc l -> string_of_int l
  | Var x -> x
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

let rec subst x y = function
  | Null
    | Loc _
    | New _ as e -> e
  | Var x' -> Var (substVar x x' y)
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

let freeVars e =
  let rec freeVars' = function
    | Null
      | Loc _
      | New _ -> []
    | Var x
      | FieldAccess (x, _) -> [x]
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

type fieldDef =
  | FieldDef of fieldName * typ

let showFieldDef (FieldDef (f, t)) = f ^ " : " ^ showType t

type methodSig =
  | MethodSig of methodName * varName * typ * typ

let showMethodSig (MethodSig(m, x, t1, t2)) =
  m ^ "(" ^ x ^ " : " ^ showType t1 ^ ") : " ^ showType t2

type methodDef =
  | MethodDef of methodSig * expr

let showMethodDef (MethodDef(msig, e)) =
  "def " ^ showMethodSig msig ^ " { " ^ showExpr e ^ " } "

type classDef =
  | ClassDef of className * interfaceName * fieldDef list * methodDef list

let rec intercalate s = function
  | [] -> ""
  | [x] -> x
  | x::xs -> x ^ s ^ intercalate s xs

let showClassDef (ClassDef(c, i, flds, mtds)) =
  let fields = intercalate " " (List.map (fun f -> showFieldDef f) flds) in
  let methods = intercalate " " (List.map (fun f -> showMethodDef f) mtds) in
  "class " ^ c ^ " implements " ^ i ^ " {" ^ fields ^ " " ^ methods ^ "}"

type interfaceDef =
  | InterfaceDef of interfaceName * methodSig list
  | ExtInterfaceDef of interfaceName * interfaceName * interfaceName

let showInterfaceDef = function
  | InterfaceDef(i, msigs) ->
     let signatures =
       intercalate " " (List.map (fun m -> showMethodSig m) msigs)
     in
     "interface " ^ i ^ " {" ^ signatures ^ "}"
  | ExtInterfaceDef(i, i1, i2) ->
     "interface " ^ i ^ " extends " ^ i1 ^ ", " ^ i2

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
