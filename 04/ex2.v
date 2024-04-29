Require Import Coq.Lists.List.
Require Import String.
Open Scope string_scope.
Import ListNotations.

Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string)
  | LetIn (x : string) (n : nat) (e : arith)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

Example ex1 := LetIn "x" 1
               (LetIn "y" 2
                 (Plus (Var "x") (Var "y"))).
Example ex2 := LetIn "x" 1
               (LetIn "y" 2
                 (Plus (Var "x") (Times (Var "y") (Var "z")))).

Infix "=?" := string_dec.
Fixpoint substitute (e1 : arith) (v : string) (e2 : arith) : arith :=
  match e1 with
  | Const _ => e1
  | Var x => if x =? v then e2 else e1
  | LetIn x e1' e2' => LetIn x e1' (substitute e2' v e2)
  | Plus pe1 pe2 => Plus (substitute pe1 v e2) (substitute pe2 v e2)
  | Times pe1 pe2 => Times (substitute pe1 v e2) (substitute pe2 v e2)
  end.

Fixpoint binding (name : string) (env : list (string * nat)) : nat :=
  match env with
  | [] => 0
  | (n, v) :: rest => if n =? name then v else binding name rest
  end.

Fixpoint eval (e : arith) (env : list (string * nat)) : nat :=
  match e with
  | Const c => c
  | Var x => binding x env
  | LetIn x n e => eval e ((x, n) :: env)
  | Plus e1 e2 => (eval e1 env) + (eval e2 env)
  | Times e1 e2 => (eval e1 env) + (eval e2 env)
  end.

(*
  let x := 1 in
    let y := 2 in
      x+y
*)
Compute eval
  (LetIn "x" 1 (LetIn "y" 2 (Plus (Var "x") (Var "y"))))
  [].
