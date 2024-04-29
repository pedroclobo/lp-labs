Theorem plus_0 : forall n : nat,
  0 + n = n.

Proof.
  intros n.
  simpl.
  reflexivity.
Qed.

(* 2.1 *)
Theorem thm_simpl1: forall a b : nat,
  a = 0 -> b * (a + b) = b * b.

Proof.
  intros a b H.
  rewrite H.
  simpl.
  reflexivity.
Qed.

(* 2.2 *)
Theorem thm_simpl2: forall (a b c d : nat) (f : nat -> nat -> nat),
    a = b -> c = d -> (forall x y, f x y = f y x) -> f a c = f d b.

Proof.
  intros a b c d f E1 E2 H.
  rewrite E1.
  rewrite E2.
  rewrite H.
  reflexivity.
Qed.

(* 2.3 *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.

Proof.
  intros f H b.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

(* 2.4 *)
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.

Proof.
  intros f H b.
  rewrite H.
  rewrite H.
  destruct b; simpl; reflexivity.
Qed.
