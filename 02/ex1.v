Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(*
  d (b a 5) -> X - missing type
  d mumble (b a 5) -> Ok
  d bool (b a 5) -> Ok
  e bool 5 -> X - 5 is not bool
  e bool true -> Ok
  e mumble (b c 0) -> Ok
  e bool (b c 0) -> X - not bool
  c -> Ok
*)