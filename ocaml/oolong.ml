open Typechecker
open Interpreter

let usage_string = Printf.sprintf "Usage: %s [options] file\n" Sys.argv.(0)

(** Toggle debug printing *)
let debug_print = ref false

(** A function to decide whether to schedule the left or right
   thread in a fork. Default is completely random *)
let scheduler = ref (fun () -> Random.bool())

(* TODO: Allow options to appear anywhere in the argument list *)
let options =
  [("--debug", Arg.Set debug_print, "Enable debug printing");
   ("--seq", Arg.Unit (fun () -> scheduler := fun () -> true), "Schedule threads sequentially")
  ]

(** [processFile name] parses, typechecks and interprets [file],
   printing the resulting configuration. *)
let processFile filename =
  let channel = open_in filename in
  let lexbuf = Lexing.from_channel channel in
  let ast = Parser.main Lexer.main lexbuf in
  let ast' = typecheck ast in
  match interpret ast' !scheduler !debug_print with
  | Done ((heap, vars, threads), steps) ->
     begin
       Printf.printf "Ran for %d steps, resulting in\n%s\n"
         steps (Threads.show threads);
       Printf.printf "Heap:\n%s\n" (Heap.show heap);
       Printf.printf "Variables:\n%s\n" (Vars.show vars);
     end
  | Blocked ((heap, vars, threads), steps) ->
     begin
       Printf.printf "Deadlocked after %d steps:\n%s\n"
         steps (Threads.show threads);
       Printf.printf "Heap:\n%s\n" (Heap.show heap);
       Printf.printf "Variables:\n%s\n" (Vars.show vars);
     end

let () =
  Random.self_init ();
  try
    if Array.length Sys.argv <= 1 then
      Arg.usage options usage_string
    else
      Arg.parse options processFile usage_string
  with
  | Typechecker.TCError msg -> print_string (msg ^ "\n"); exit(1)
  | Parser.Error -> Printf.printf "Error during parsing\n"; exit(1)
  (* TODO: Produce more helpful error messages *)