Inductive tm : Type :=
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm
  | geq : tm -> tm -> tm.

Declare Custom Entry tm.
Declare Scope tm_scope.
Notation "'true'"  := true (at level 1): tm_scope.
Notation "'true'" := (tru) (in custom tm at level 0): tm_scope.
Notation "'false'"  := false (at level 1): tm_scope.
Notation "'false'" := (fls) (in custom tm at level 0): tm_scope.
Notation "<{ e }>" := e (e custom tm at level 99): tm_scope.
Notation "( x )" := x (in custom tm, x at level 99): tm_scope.
Notation "x" := x (in custom tm at level 0, x constr at level 0): tm_scope.
Notation "'0'" := (zro) (in custom tm at level 0): tm_scope.
Notation "'0'"  := 0 (at level 1): tm_scope.
Notation "'succ' x" := (scc x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'pred' x" := (prd x) (in custom tm at level 90, x custom tm at level 80): tm_scope.
Notation "'iszero' x" := (iszro x) (in custom tm at level 80, x custom tm at level 70): tm_scope.
Notation "'if' c 'then' t 'else' e" := (ite c t e)
                 (in custom tm at level 90, c custom tm at level 80,
                  t custom tm at level 80, e custom tm at level 80): tm_scope.
(* write a notation for geq *)
Notation "'geq' t1 t2" := (geq t1 t2) (in custom tm at level 90) : tm_scope.

(* Declare Scope tm_scope. *)
Local Open Scope tm_scope.

(* The boolean values are `true` and `false` *)
Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue tru
  | bv_false : bvalue fls.

(* The numeric values are `0` and `succ t` where `t` is a numeric value. *)
Inductive nvalue : tm -> Prop :=
  | nv_0 : nvalue <{ 0 }>
  | nv_succ : forall t, nvalue t -> nvalue <{ succ t }>.

Definition value (t : tm) := bvalue t \/ nvalue t.

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : forall t1 t2,
      <{ if true then t1 else t2 }> --> t1
  | ST_IfFalse : forall t1 t2,
      <{ if false then t1 else t2 }> --> t2
  | ST_If : forall c c' t2 t3,
      c --> c' ->
      <{ if c then t2 else t3 }> --> <{ if c' then t2 else t3 }>
  | ST_Succ : forall t1 t1',
      t1 --> t1' ->
      <{ succ t1 }> --> <{ succ t1' }>
  | ST_Pred0 :
      <{ pred 0 }> --> <{ 0 }>
  | ST_PredSucc : forall v,
      nvalue v ->
      <{ pred (succ v) }> --> v
  | ST_Pred : forall t1 t1',
      t1 --> t1' ->
      <{ pred t1 }> --> <{ pred t1' }>
  | ST_Iszero0 :
      <{ iszero 0 }> --> <{ true }>
  | ST_IszeroSucc : forall v,
       nvalue v ->
      <{ iszero (succ v) }> --> <{ false }>
  | ST_Iszero : forall t1 t1',
      t1 --> t1' ->
      <{ iszero t1 }> --> <{ iszero t1' }>
  | ST_GEq1 : forall t1 t1' t2,
      t1 --> t1' ->
      <{ geq t1 t2 }> --> <{ geq t1' t2 }>
  | ST_GEq2 : forall v1 t2 t2',
      nvalue v1 ->
      t2 --> t2' ->
      <{ geq v1 t2 }> --> <{ geq v1 t2' }>
  | ST_GEqEqual : forall v,
      nvalue v ->
      <{ geq v v }> --> <{ true }>
  | ST_GEqSuccV : forall v,
      nvalue v ->
      <{ geq v (succ v) }> --> <{ false }>
  | ST_GEqVSucc : forall v,
      nvalue v ->
      <{ geq (succ v) v }> --> <{ true }>
  | ST_GEqLeftZero : forall v,
      nvalue v ->
      <{ geq 0 v }> --> <{ false }>
  | ST_GEqRightZero : forall v,
      nvalue v ->
      <{ geq v 0 }> --> <{ true }>

where "t '-->' t'" := (step t t').

Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " tm '-->*' tm' " :=
  (multi step tm tm')
  (at level 40).

Example test_step_geq_1 :
  <{ geq 0 (succ 0) }> -->* <{ false }>.
Proof.
  eapply multi_step.
  - apply ST_GEqLeftZero. apply nv_succ. apply nv_0.
  - eapply multi_refl.
Qed.

(* Typing *)
Inductive ty : Type :=
  | Bool : ty
  | Nat : ty.

Reserved Notation "'|--' t '\in' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True :
       |-- <{ true }> \in Bool
  | T_False :
       |-- <{ false }> \in Bool
  | T_If : forall t1 t2 t3 T,
       |-- t1 \in Bool ->
       |-- t2 \in T ->
       |-- t3 \in T ->
       |-- <{ if t1 then t2 else t3 }> \in T
  | T_0 :
       |-- <{ 0 }> \in Nat
  | T_Succ : forall t1,
       |-- t1 \in Nat ->
       |-- <{ succ t1 }> \in Nat
  | T_Pred : forall t1,
       |-- t1 \in Nat ->
       |-- <{ pred t1 }> \in Nat
  | T_Iszero : forall t1,
       |-- t1 \in Nat ->
       |-- <{ iszero t1 }> \in Bool
  | T_GEq : forall t1 t2,
       |-- t1 \in Nat ->
       |-- t2 \in Nat ->
       |-- <{ geq t1 t2 }> \in Bool

  where "'|--' t '\in' T" := (has_type t T).

Hint Constructors has_type : core.

Example has_type_1 :
  |-- <{ if true then succ (succ 0) else 0 }> \in Nat.
Proof.
  apply T_If.
  - apply T_True.
  - repeat (apply T_Succ). apply T_0.
  - apply T_0.
Qed.

Example has_type_2 :
  |-- <{ if iszero 0 then succ 0 else pred 0 }> \in Nat.
Proof.
  apply T_If.
  - apply T_Iszero. apply T_0.
  - apply T_Succ. apply T_0.
  - apply T_Pred. apply T_0.
Qed.

Example has_type_3 :
  |-- <{ if iszero (succ 0) then succ 0 else pred (succ 0) }> \in Nat.
Proof.
  apply T_If.
  - apply T_Iszero. apply T_Succ. apply T_0.
  - apply T_Succ. apply T_0.
  - apply T_Pred. apply T_Succ. apply T_0.
Qed.

Example has_type_4 :
  |-- <{ if iszero 0 then iszero (pred 0) else false }> \in Bool.
Proof.
  apply T_If.
  - apply T_Iszero. apply T_0.
  - apply T_Iszero. apply T_Pred. apply T_0.
  - apply T_False.
Qed.

Example has_type_5 :
  |-- <{ if iszero (succ 0) then succ 0
         else if true then succ (succ 0)
         else 0 }> \in Nat.
Proof.
  apply T_If.
  - apply T_Iszero. apply T_Succ. apply T_0.
  - apply T_Succ. apply T_0.
  - apply T_If.
    -- apply T_True.
    -- repeat (apply T_Succ). apply T_0.
    -- apply T_0.
Qed.


Example has_type_geq :
  |-- <{ if true then geq 0 (succ (succ 0))
         else geq (succ 0) 0}> \in Bool.
Proof.
  apply T_If.
  - apply T_True.
  - apply T_GEq.
    -- apply T_0.
    -- repeat (apply T_Succ). apply T_0.
  - apply T_GEq.
    -- apply T_Succ. apply T_0.
    -- apply T_0.
Qed.
