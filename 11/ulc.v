Require Import Coq.Strings.String.

Inductive tm : Type :=
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> tm -> tm.

Declare Custom Entry stlc.
Notation "<{  e  }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "'λ' x . y" :=
  (tm_abs x y) (in custom stlc at level 90, x at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Definition b : string := "b".
Definition f : string := "f".
Definition p : string := "p".
Definition q : string := "q".
Definition t : string := "t".
Definition w : string := "w".
Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{ λ y . t1 }> =>
      if String.eqb x y then t else <{ λ y . [x:=s] t1 }>
  | <{ t1 t2 }> =>
      <{ ([x:=s] t1) ([x:=s] t2) }>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x t1 t2,
         <{ (λ x . t1) t2 }> --> <{ [x:=t2]t1 }>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{ t1 t2 }> --> <{ t1' t2 }>
  | ST_App2 : forall t1 t2 t2',
         t2 --> t2' ->
         <{ t1 t2 }> --> <{ t1  t2' }>

where "t '-->' t'" := (step t t').

Hint Constructors step : core.

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).
