Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition weekday_to_nat (d : day) : nat :=
    match d with
    | sunday => 1
    | monday => 2
    | tuesday => 3
    | wednesday => 4
    | thursday => 5
    | friday => 6
    | saturday => 7
    end.

Compute (weekday_to_nat friday).

Definition is_weekend (d : day) : bool :=
    match d with
    | saturday => true
    | sunday => true
    | _ => false
    end.
