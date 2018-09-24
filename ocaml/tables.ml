open Ast

module ClassTable = Map.Make(String)
type classTable = classDef ClassTable.t

let rec buildClassTable = function
  | [] -> ClassTable.empty
  | ClassDef(key, _, _, _) as c :: cs ->
     ClassTable.add key c (buildClassTable cs)

let lookupClass ctable c = ClassTable.find_opt c ctable

module InterfaceTable = Map.Make(String)
type interfaceTable = Ast.interfaceDef InterfaceTable.t

let rec buildInterfaceTable = function
  | [] -> InterfaceTable.empty
  | i :: is ->
     let key = match i with
       | InterfaceDef(i, _) -> i
       | ExtInterfaceDef(i, _, _) -> i
     in
     InterfaceTable.add key i (buildInterfaceTable is)

let lookupInterface itable i = InterfaceTable.find_opt i itable
