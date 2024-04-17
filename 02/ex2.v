Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.

(* 2.1 *)
(* {T : Type} makes the type implicit *)
Definition my_tl {T : Type} (l : list T) : list T :=
  match l with
  | [] => []
  | _ :: t => t
  end.

Compute (my_tl [1;2;3]).
Compute (my_tl [false;true;false]).

(* 2.2 *)
Fixpoint remove_last {T : Type} (l : list T) : list T :=
  match l with
  | [] => []
  | [x] => []
  | h :: t => h :: (remove_last t)
  end.

Compute (remove_last ([1;2;3])).

(* 2.3 *)
Definition first_n {T : Type} (n : nat) (l : list T) : list T :=
  let fix aux {T : Type} (n : nat) (l : list T) (acc : list T) : list T :=
    match n, l with
    | 0, _ => acc
    | _, [] => acc
    | _, h :: t => aux (n - 1) t (app acc [h])
    end
  in aux n l [].

Compute (first_n 2 [1;2;3]).

(* 2.4 *)
Fixpoint skip_n {T : Type} (n : nat) (l : list T) : list T :=
  match n, l with
  | 0, l => l
  | _, [] => []
  | _, _ :: t => skip_n (n - 1) t
  end.

Compute (skip_n 3 [1;2;3;4;5]).

(* 2.5 *)
Fixpoint last {T : Type} (l : list T) : option T :=
  match l with
  | [] => None
  | [_ ; s] => Some s
  | _ :: t => last t
  end.

Compute (last []).
Compute (last [1;2;3]).

(* 2.6 *)
(*
We have to use S n as otherwise Coq can't
determine that there is a decreasing argument.
*)
Fixpoint seq (s : nat) (l : nat) : list nat :=
  match l with
  | 0 => []
  | S i => s :: seq (s + 1) i
  end.

Compute (seq 3 4).
Compute (seq 10 10).

(* 2.8 *)
Fixpoint append {T:Type} (l1 : list T) (l2 : list T) : list T :=
  match l1, l2 with
  | [], [] => []
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, _ => h1 :: append t1 l2
  end.

Compute (append [1;2;3] [4;5;6]).

(* 2.7 *)
Definition my_split {T1 T2 : Type} (p : list (T1 * T2)) :=
  let fix aux {T1 T2 : Type} (p : list (T1 * T2)) (acc : (list T1) * (list T2)) :=
    match p with
    | [] => acc
    | (p11, p12) :: rest => aux rest (append (fst acc) [p11], append (snd acc) [p12])
    end
  in aux p ([], []).

Compute (my_split [(1, 2); (3, 4); (5, 6)]).
Compute (my_split [(1,true); (2,false); (3,true)]).

(* 2.9 *)
Fixpoint rev {T : Type} (l : list T) : list T :=
  match l with
  | [] => []
  | h :: t => append (rev t) [h]
  end.

Compute (rev [1;2;3]).

(* 2.10 *)
Fixpoint existsb {T : Type} (p : T -> bool) (l : list T) : bool :=
  match l with
  | [] => false
  | h :: t => p h || existsb p t
  end.

Compute (existsb (fun e => e <=? 3) [2;4;5]).

(* 2.11 *)
Fixpoint forallb {T : Type} (p : T -> bool) (l : list T) : bool :=
  match l with
  | [] => true
  | h :: t => p h && forallb p t
  end.

Compute (forallb (fun e => e <=? 3) [2;4;5]).

(* 2.12 *)
Fixpoint find {T : Type} (p : T -> bool) (l : list T) : option T :=
  match l with
  | [] => None
  | h :: t => if p h then Some h else find p t
  end.

Compute (find (fun e => e <=? 3) [6;4;1;3;7]).
Compute (find (fun e => e <=? 3) [6;4;4;5;7]).

(* 2.13 *)
Definition partition {X : Type} (p : X -> bool) (l : list X) : (list X * list X) :=
  let fix aux {X : Type} (p : X -> bool) (l : list X) (acc : (list X * list X)) : (list X * list X) :=
    match l with
    | [] => acc
    | h :: t => aux p t
      (if p h then
        (append (fst acc) [h], snd acc)
      else
        (fst acc, append (snd acc) [h]))
    end
  in
  aux p l ([], []).

Compute (partition (fun e => e <=? 3) [6;4;1;3;7]).

(* 2.14 *)
Fixpoint list_prod_aux {T1 T2 : Type} (l1 : list T1) (l2 : list T2) (acc : list (T1 * T2)): list (T1 * T2) :=
  match l1, l2 with
  | [], [] | [], _ | _, [] => acc
  | h1 :: t1, h2 :: t2 => list_prod_aux t1 l2 (append acc [(h1, h2)])
  end.

Compute (list_prod [1; 2] [true; false]).
Compute (list_prod [1; 2; 3] [true; false; true]).
