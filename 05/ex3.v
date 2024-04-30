(* 3.1 *)
(*
  The Imp language supports loops. In Coq, all functions must be total
  (all functions must terminate). By calling `exec` on a program of
  the type _while true do skip end_, the function will not terminate.
*)

(* 3.2 *)
(*
  A step-index evaluator is a function that takes a program and a
  step index and returns the state of the program after the given
  number of steps. The step-index evaluator is a total function,
  as it will always terminate after the given number of steps.
*)
