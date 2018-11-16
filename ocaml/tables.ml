open Ast

(** This module defines operations on class and interface tables. *)
module Table(M : sig type v val getKey : v -> string end) = struct
  module TableImpl = Map.Make(String)

  type table = M.v TableImpl.t

  (** [build l] takes a list of [v]s and builds a lookup table
     containing each element of [l], where the keys are extracted
     using [M.getkey]. *)
  let rec build = function
    | [] -> TableImpl.empty
    | x :: xs -> TableImpl.add (M.getKey x) x (build xs)

  (** [lookup k t] returns [Some v] if [k] maps to [v] in [t], or
     [None] otherwise. *)
  let lookup = TableImpl.find_opt

  (** [get k t] returns [v] if [k] maps to [v] in [t], or raises
     an exception otherwise. *)
  let get = TableImpl.find
end

module ClassTable =
  Table(struct type v = classDef let getKey = getClassName end)
type classTable = ClassTable.table

module InterfaceTable =
  Table(struct type v = interfaceDef let getKey = getInterfaceName end)
type interfaceTable = InterfaceTable.table