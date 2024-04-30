From Lab5 Require Import Maps.
Require Import PeanoNat.

Definition valuation := partial_map nat.
Notation var := string.

(* 1.1 *)
Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | And (b1 b2 : bexp)
  | Neg (b : bexp)
  | Eqq (e1 e2 : arith).

Inductive cmd : Type :=
  | Skip
  | Assign (x : var) (e : arith)
  | Sequence (c1 c2 : cmd)
  | If (b : bexp) (c1 c2 : cmd).

(* 1.2 *)
(* bexp *)
Declare Scope imp_scope.

Notation "'true'" := BTrue (at level 0) : imp_scope.
Notation "'false'" := BFalse (at level 0) : imp_scope.
Infix "&&" := And (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (Neg b) (at level 75, right associativity) : imp_scope.
Notation "x == y" := (Eqq x y) (at level 70, no associativity) : imp_scope.

(* arith *)
Infix "+" := Plus (at level 50, left associativity) : imp_scope.
Infix "*" := Times (at level 40, left associativity) : imp_scope.

(* cmd *)
Notation "'skip'" := Skip (at level 0) : imp_scope.
Infix "<-" := Assign (at level 0, no associativity) : imp_scope.
Notation "x ; y" := (Sequence x y) (at level 90, right associativity) : imp_scope.
Notation "'test' x 'then' y 'else' z 'end'" :=
  (If x y z)
    (at level 89, x at level 99,
     y at level 99, z at level 99) : imp_scope.

(* 1.3 *)
Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.

Fixpoint aeval (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x => match v x with
             | Some n => n
             | None => 0
             end
  | Plus e1 e2 => aeval e1 v + aeval e2 v
  | Times e1 e2 => aeval e1 v * aeval e2 v
  end.

Fixpoint beval (b : bexp) (v : valuation) : bool :=
  match b with
  | BTrue => Coq.Init.Datatypes.true
  | BFalse => Coq.Init.Datatypes.false
  | And b1 b2 => beval b1 v && beval b2 v
  | Neg b => negb (beval b v)
  | Eqq e1 e2 => (aeval e1 v) =? (aeval e2 v)
  end.

Fixpoint exec (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => t_update v x (Some (aeval e v))
  | Sequence c1 c2 => exec c2 (exec c1 v)
  | If b c1 c2 => if (beval b v)
                  then (exec c1 v)
                  else (exec c2 v)
  end.


Open Scope imp_scope.
Open Scope string_scope.

(* x := 5 *)
Compute (exec ("x" <- 5) empty) "x".

(* x := 5 + 3 *)
Compute (exec ("x" <- (5 + 3)) empty) "x".

(* if true then x := 5 else x := 3 end *)
Compute (exec (test BTrue then "x" <- 5 else "x" <- 3 end) empty) "x".

(* if false then x := 5 else x := 3 end *)
Compute (exec (test BFalse then "x" <- 5 else "x" <- 3 end) empty) "x".

(* (x := 5; if x := 5 then x := x * 5 else x := x * 3 end) *)
Compute (exec (
  "x" <- 5;
  test (Eqq "x" 5) then "x" <- ("x" * 5) else "x" <- ("x" * 3) end
) empty) "x".
