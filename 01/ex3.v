Module NatPlayground.

(* 3.1 *)
Inductive nat : Type :=
    | O : nat
    | S (n : nat).

End NatPlayground.

(* 3.2 *)
Definition minustwo n :=
    match n with
    | O | S O => O
    | S (S n') => n'
    end.

Example test_minustwo_1 : (minustwo 2) = 0.
Proof. simpl. reflexivity. Qed.

Example test_minustwo_2 : (minustwo 3) = 1.
Proof. simpl. reflexivity. Qed.

(* 3.3 *)
Fixpoint evenb n :=
    match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
    end.

Example test_evenb_1 : (evenb O) = true.
Proof. simpl. reflexivity. Qed.

Example test_evenb_2 : (evenb 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_evenb_3 : (evenb 3) = false.
Proof. simpl. reflexivity. Qed.

(* 3.3 *)
Fixpoint oddb_rec n :=
    match n with
    | O => false
    | S O => true
    | S (S n') => oddb_rec n'
    end.

Example test_oddb_rec_1 : (oddb_rec 0) = false.
Proof. simpl. reflexivity. Qed.

Example test_oddb_rec_2 : (oddb_rec 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_oddb_rec_3 : (oddb_rec 3) = true.
Proof. simpl. reflexivity. Qed.

(* 3.4 *)
Definition oddb n :=
    negb (evenb n).

Example test_oddb_1 : (oddb 0) = false.
Proof. simpl. reflexivity. Qed.

Example test_oddb_2 : (oddb 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_oddb_3 : (oddb 3) = true.
Proof. simpl. reflexivity. Qed.

(* 3.5 *)
Fixpoint plus n1 n2 :=
    match n1 with
    | O => n2
    | S n1' => S (plus n1' n2)
    end.

(* Define notation for plus *)
Notation "x + y" := (plus x y) (at level 50, left associativity).

Example test_plus_1 : (0 + 0) = 0.
Proof. simpl. reflexivity. Qed.

Example test_plus_2 : (0 + 1) = 1.
Proof. simpl. reflexivity. Qed.

Example test_plus_3 : (1 + 1) = 2.
Proof. simpl. reflexivity. Qed.

Example test_plus_4 : (2 + 1) = 3.
Proof. simpl. reflexivity. Qed.

(*
    If n1 is 0, res = 0
    Otherwise, res = n2 + (n1 - 1) * n2
*)
Fixpoint mul n1 n2 :=
    match n1 with
    | O => O
    | S n1' => n2 + (mul n1' n2)
    end.

Notation "x * y" := (mul x y) (at level 40, left associativity).

Example test_mul_1 : (0 * 0) = 0.
Proof. simpl. reflexivity. Qed.

Example test_mul_2 : (1 * 1) = 1.
Proof. simpl. reflexivity. Qed.

Example test_mul_3 : (2 * 2) = 4.
Proof. simpl. reflexivity. Qed.

Fixpoint exp (n1 : nat) (n2 : nat) :=
    match n2 with
    | O => S O
    | S n2' => n1 * (exp n1 n2')
    end.

Notation "x ^ y" := (exp x y) (at level 30, right associativity).

Example test_exp_1 : (1 ^ 0) = 1.
Proof. simpl. reflexivity. Qed.

Example test_exp_2 : (0 ^ 1) = O.
Proof. simpl. reflexivity. Qed.

Example test_exp_3 : (1 ^ 1) = 1.
Proof. simpl. reflexivity. Qed.

Example test_exp_4 : (2 ^ 2) = 4.
Proof. simpl. reflexivity. Qed.

Example test_exp_5 : (2 ^ 3) = 8.
Proof. simpl. reflexivity. Qed.

(* 3.6 *)
(*      plus 3 2
   i.e. plus (S (S (S O))) (S (S O))
    ==> S (plus (S (S O)) (S (S O)))
          by the second clause of the match
    ==> S (S (plus (S O) (S (S O))))
          by the second clause of the match
    ==> S (S (S (plus O (S (S O)))))
          by the second clause of the match
    ==> S (S (S (S (S O))))
          by the first clause of the match
   i.e. 5  *)

(* 3.6 *)
Fixpoint factorial n :=
    match n with
    | O | S O => S O
    | S n1' => n * (factorial n1')
    end.

Example test_factorial_1 : factorial 0 = 1.
Proof. simpl. reflexivity. Qed.

Example test_factorial_2 : factorial 1 = 1.
Proof. simpl. reflexivity. Qed.

Example test_factorial_3 : factorial 2 = 2.
Proof. simpl. reflexivity. Qed.

Example test_factorial_4 : factorial 3 = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial_5 : factorial 5 = 120.
Proof. simpl. reflexivity. Qed.
