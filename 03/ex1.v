Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* 1.1 *)
Definition partition {X : Type} (p : X -> bool) (l : list X) : (list X * list X) :=
  (filter p l, filter (fun x => negb (p x)) l).

Compute partition (fun e => e <=? 3) [6;4;1;3;7].

(* 1.2 *)
Fixpoint my_list_prod { T1 T2 : Type } (l1 : list T1) (l2 : list T2) : list (T1 * T2) :=
  match l1 with
  | [] => []
  | h1 :: r1 => map (fun x => (h1, x)) l2 ++ my_list_prod r1 l2
  end.

Compute my_list_prod [1; 2] [true; false].

(* 1.3 *)
Definition my_length { X : Type } (l : list X) : nat :=
  fold_right (fun _ acc => acc + 1) 0 l.

Compute (my_length []).
Compute (my_length [1;2;3]).

(* 1.4 *)
Definition my_map { X Y : Type } (f : X -> Y) (l : list X) : list Y :=
  fold_right (fun x acc => f x :: acc) [] l.

Compute (my_map (fun x => x + 1) [1;2;3]).

(* 1.5 *)
Definition my_filter { X : Type } (p : X -> bool) (l : list X) : list X :=
  fold_right (fun x acc => (if p x then (x :: acc) else acc)) [] l.

Compute (my_filter (fun x => x <=? 3) [1;2;3;4;5]).

(* 1.6 *)
Definition forallb {T : Type} (p : T -> bool) (l : list T) : bool :=
  fold_right (fun x acc => andb (p x) acc) true l.

Compute (forallb (fun e => e <=? 3) [2;4;5]).
Compute (forallb (fun e => e <=? 3) [2;1;1]).
