From Lab11 Require Import ulc.
Require Import Coq.Strings.String.
Require Import Coq.Lists.ListSet.

Definition set_add := set_add string_dec.
Definition set_diff := set_diff string_dec.
Definition set_union := set_union string_dec.

(* Returns the set of bound variables *)
Fixpoint BV (t : tm) : set string :=
  match t with
  | tm_var x => nil
  | <{ t1 t2 }> => set_union (BV t1) (BV t2)
  | <{ λ x . t }> => set_add x (BV t)
  end.

Compute (BV <{ λ x . x}>).
Compute (BV <{ λ x . λ y . x}>).

(* Returns the set of free variables *)
Definition FV (t : tm) : list string :=
  let fix AV (t : tm) : list string :=
    match t with
    | tm_var x => set_add x (empty_set string)
    | <{ t1 t2 }> => set_union (AV t1) (AV t2)
    | <{ λ x . t }> => set_add x (AV t)
    end
  in
    set_diff (AV t) (BV t).

Compute (FV <{λ x . x}>).
Compute (FV <{λ x . λ y . x}>).
Compute (FV <{λ x . λ y . x y w}>).


(*
  1. (x (λ  x y . x)) : open term
  2. λ  x . (x (λ  x y . x)) : closed term
  3. λ  x y . x y z : open term
  4. λ  x y . λ  z . z y : closed term
  5. λ  x y . λ  z . z (λ  x y . w) : open term
*)