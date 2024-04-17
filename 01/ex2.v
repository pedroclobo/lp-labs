Inductive bool : Type :=
    | true : bool
    | false : bool.

Definition negb (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.

Definition andb (b1 b2 : bool) : bool :=
    match (b1, b2) with
    | (true, true) => true
    | (true, false) => false
    | (false, true) => false
    | (false, false) => false
    end.

Example test_andb1 : (andb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb2 : (andb true false) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb3 : (andb false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb4 : (andb false false) = false.
Proof. simpl. reflexivity. Qed.

Definition orb (b1 b2 : bool) : bool :=
    match (b1, b2) with
    | (true, true) => true
    | (true, false) => true
    | (false, true) => true
    | (false, false) => false
    end.

Example test_orb1 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2 : (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb3 : (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4 : (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "~ x" := (negb x).
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Definition xor (b1 b2 : bool) : bool :=
    match (b1, b2) with
    | (true, true) => false
    | (true, false) => true
    | (false, true) => true
    | (false, false) => false
    end.

Example test_xor1 : (xor true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_xor2 : (xor true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_xor3 : (xor false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_xor4 : (xor false false) = false.
Proof. simpl. reflexivity. Qed.
