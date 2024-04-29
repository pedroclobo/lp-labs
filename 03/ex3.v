Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Nat.
Import ListNotations.

Inductive Tree (X : Type) : Type :=
  | Empty
  | Node : X -> Tree X -> Tree X -> Tree X.

(* Make Empty and Node type argument implicit *)
Arguments Empty {X}.
Arguments Node {X} _ _ _.

Definition tree := Node 1 (Node 2 Empty Empty) (Node 3 Empty Empty).

(* 3.1 *)
Fixpoint nodes {X : Type} (t : Tree X) : nat :=
  match t with
  | Empty => 0
  | Node _ l r => 1 + nodes l + nodes r
  end.

Compute nodes tree.

(* 3.2 *)
Fixpoint leaves {X : Type} (t : Tree X) : nat :=
  match t with
  | Empty => 0
  | Node _ Empty Empty => 1
  | Node _ l r => leaves l + leaves r
  end.

Compute leaves tree.

(* 3.3 *)
Fixpoint flatten {X : Type} (t : Tree X) : list X :=
  match t with
  | Empty => []
  | Node x l r => x :: (flatten l ++ flatten r)
  end.

Compute flatten tree.

(* 3.4 *)
Fixpoint height {X : Type} (t : Tree X) : nat :=
  match t with
  | Empty => 0
  | Node _ l r => S (max (height l) (height r))
  end.

Compute height tree.

(* 3.5 *)
Theorem height_at_most_number_nodes_tree {X : Type}: forall t : Tree X,
  height t <= nodes t.

Proof.
  induction t.
  - simpl. reflexivity.
  - simpl. lia.
Qed.

(* 3.6 *)
Fixpoint maxTree (t : Tree nat) : nat :=
  match t with
  | Empty => 0
  | Node x l r => max x (max (maxTree l) (maxTree r))
  end.

Compute maxTree tree.

(* 3.7 *)
Fixpoint subTrees {X : Type} (t : Tree X) : list (Tree X) :=
  match t with
  | Empty => [Empty]
  | Node _ l r => t :: subTrees l ++ subTrees r
  end.

Compute subTrees tree.

(* 3.8 *)
Fixpoint mapBTree {X Y : Type} (p : X -> Y) (t : Tree X) : Tree Y :=
  match t with
  | Empty => Empty
  | Node x l r => Node (p x) (mapBTree p l) (mapBTree p r)
  end.

Compute mapBTree (fun x => x + 1) tree.

(* 3.9 *)
Fixpoint foldBTree {X Y : Type} (f : X -> Y -> Y -> Y) (y : Y) (t : Tree X) : Y :=
  match t with
  | Empty => y
  | Node x l r => f x (foldBTree f y l) (foldBTree f y r)
  end.

(* 3.10 *)
Definition nodes' {X : Type} (t : Tree X) : nat :=
  foldBTree (fun _ l r => 1 + l + r) 0 t.

Compute nodes' tree.

Definition height' {X : Type} (t : Tree X) : nat :=
  foldBTree (fun _ l r => S (max l r)) 0 t.

Compute height' tree.

Definition flatten' {X : Type} (t : Tree X) : list X :=
  foldBTree (fun x l r => x :: l ++ r) [] t.

Compute flatten' tree.

Definition maxTree' (t : Tree nat) : nat :=
  foldBTree (fun x l r => max x (max l r)) 0 t.

Compute maxTree' tree.

Definition mapBTree' {X Y : Type} (p : X -> Y) (t : Tree X) : Tree Y :=
  foldBTree (fun x l r => Node (p x) l r) Empty t.

Compute mapBTree' (fun x => x + 1) tree.

(* 3.11 *)
(*
  The composition of maps of the two functions
  is equivalent to the map of the composition of the two functions.
*)
Lemma mapfusion : forall {X Y Z : Type} (f : Y -> Z) (g : X -> Y) tree,
  mapBTree f (mapBTree g tree) = mapBTree (fun x => f (g x)) tree.

Proof.
  intros. induction tree0.
  - simpl. reflexivity.
  - simpl. rewrite IHtree0_1. rewrite IHtree0_2. reflexivity.
Qed.
