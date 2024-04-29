Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import String.
Open Scope string_scope.
Require Import Lia.
Require Import Arith.
Import ListNotations.

Inductive arith : Type :=
  | Const (n : nat)
  | Var (x : string)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

(* 1.1 *)
Fixpoint size (tree : arith) : nat :=
  match tree with
  | Const _ | Var _ => 1
  | Plus l r | Times l r => 1 + size l + size r
  end.

Fixpoint depth (tree : arith) : nat :=
  match tree with
  | Const _ | Var _ => 1
  | Plus l r | Times l r => 1 + max (depth l) (depth r)
  end.

(* 1.2 *)
Theorem depth_le_size : forall e, depth e <= size e.
Proof.
  intros. induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. lia.
  - simpl. lia.
Qed.

(* 1.3 *)
Fixpoint commuter (tree : arith) : arith :=
  match tree with
  | Const _ | Var _ => tree
  | Plus l r => Plus (commuter r) (commuter l)
  | Times l r => Times (commuter r) (commuter l)
  end.

Compute commuter (Plus (Const 1) (Times (Const 2) (Const 3))).

(* 1.4 *)
Lemma plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn. rewrite plus_n_Sm. reflexivity.
Qed.

(* 1.4.1 *)
(*
  The size of a commuted tree
  must be equal to the size of the original tree.
 *)
Theorem size_commuter : forall e, size (commuter e) = size e.
Proof.
  intros e.
  induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. rewrite plus_comm. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. rewrite plus_comm. reflexivity.
Qed.

(* 1.4.2 *)
(*
  The depth of a commuted tree
  must be equal to the depth of the original tree.
 *)
Theorem depth_commuter : forall e, depth (commuter e) = depth e.
Proof.
  induction e; simpl; lia.
Qed.

(* 1.4.3 *)
(* The commutaion of a commutation of a tree yields the original tree. *)
Theorem commuter_inverse : forall e, commuter (commuter e) = e.
Proof.
  intros e.
  induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  - simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

(* 1.5 *)
Infix "=?" := string_dec.
Fixpoint substitute (e1 : arith) (v : string) (e2 : arith) : arith :=
  match e1 with
  | Const _ => e1
  | Var x => if x =? v then e2 else e1
  | Plus pe1 pe2 => Plus (substitute pe1 v e2) (substitute pe2 v e2)
  | Times pe1 pe2 => Times (substitute pe1 v e2) (substitute pe2 v e2)
  end.

Compute substitute (Plus (Var "x") (Var "y")) "x" (Const 42).

(* 1.6 *)
(* 1.6.1 *)
(*
  When performing a substitution, the depth of the resulting tree
  is, at most, the sum of the depth of the tree with the original expression
  and the depth of the tree with the target expression.
 *)
Theorem substitute_depth : forall replaceThis withThis inThis,
        depth (substitute inThis replaceThis withThis)
        <= depth inThis + depth withThis.

Proof.
  induction inThis; simpl.
  - lia.
  - destruct (x =? replaceThis); simpl; lia.
  - lia.
  - lia.
Qed.

(* 1.6.2 *)
(*
  Replcaing `replaceThis` in `inThis` by `replaceThis`
  yields the original arith.
*)
Theorem substitute_self : forall replaceThis inThis,
  substitute inThis replaceThis (Var replaceThis) = inThis.

Proof.
  induction inThis.
  - simpl. reflexivity.
  - simpl. destruct (x =? replaceThis). rewrite e. reflexivity. reflexivity.
  - simpl. rewrite IHinThis1. rewrite IHinThis2. reflexivity.
  - simpl. rewrite IHinThis1. rewrite IHinThis2. reflexivity.
Qed.

(* 1.6.3 *)
(*
  Substitution and commutation are commutable.
*)
Theorem substitute_commuter : forall replaceThis withThis inThis,
    commuter (substitute inThis replaceThis withThis)
  = substitute (commuter inThis) replaceThis (commuter withThis).

Proof.
  induction inThis.
  - simpl. reflexivity.
  - simpl. destruct (x =? replaceThis). reflexivity. simpl. reflexivity.
  - simpl. rewrite IHinThis1. rewrite IHinThis2. reflexivity.
  - simpl. rewrite IHinThis1. rewrite IHinThis2. reflexivity.
Qed.

(* 1.7 *)
Fixpoint binding (name : string) (env : list (string * nat)) : nat :=
  match env with
  | [] => 0
  | (n, v) :: rest => if n =? name then v else binding name rest
  end.

Fixpoint eval (e : arith) (env : list (string * nat)) : nat :=
  match e with
  | Const c => c
  | Var x => binding x env
  | Plus e1 e2 => (eval e1 env) + (eval e2 env)
  | Times e1 e2 => (eval e1 env) + (eval e2 env)
  end.

Compute eval (Plus (Var "x") (Const 1)) [("x", 2)].
