Require Import Coq.Arith.Arith.
Require Import String.
From Lab10 Require Import Imp Maps.

Reserved Notation " a '/' st '-->a' a' "
                  (at level 40, st at level 39).
Reserved Notation " b '/' st '-->b' b' "
                  (at level 40, st at level 39).
Reserved Notation " t '/' st '-->' t' '/' st' "
                  (at level 40, st at level 39, t' at level 39).

(* Values are ANum's *)
Inductive aval : aexp -> Prop :=
  | av_num : forall n, aval (ANum n).

(* Small-step evaluation relation for arithmetic expressions *)
Inductive astep : state -> aexp -> aexp -> Prop :=
  (* Identifier steps to a value with the given identifier evaluated in the state *)
  | AS_Id : forall st i,
      AId i / st -->a ANum (st i)
  (* Reduce the first operand *)
  | AS_Plus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (APlus a1 a2) / st -->a (APlus a1' a2)
  (* Reduce the second operand, as the first is already a value *)
  | AS_Plus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (APlus v1 a2) / st -->a (APlus v1 a2')
  (* Final reduction, both operands are values *)
  | AS_Plus : forall st n1 n2,
      APlus (ANum n1) (ANum n2) / st -->a ANum (n1 + n2)
  (* Reduce the first operand *)
  | AS_Minus1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMinus a1 a2) / st -->a (AMinus a1' a2)
  (* Reduce the second operand, as the first is already a value *)
  | AS_Minus2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMinus v1 a2) / st -->a (AMinus v1 a2')
  (* Final reduction, both operands are values *)
  | AS_Minus : forall st n1 n2,
      (AMinus (ANum n1) (ANum n2)) / st -->a (ANum (minus n1 n2))
  (* Reduce the first operand *)
  | AS_Mult1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (AMult a1 a2) / st -->a (AMult a1' a2)
  (* Reduce the second operand, as the first is already a value *)
  | AS_Mult2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (AMult v1 a2) / st -->a (AMult v1 a2')
  (* Final reduction, both operands are values *)
  | AS_Mult : forall st n1 n2,
      (AMult (ANum n1) (ANum n2)) / st -->a (ANum (mult n1 n2))

  where " t '/' st '-->a' t' " := (astep st t t').


(* Small-step evaluation relation for boolean expressions *)
Inductive bstep : state -> bexp -> bexp -> Prop :=
  | BS_Eq1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (BEq a1 a2) / st -->b (BEq a1' a2)
  | BS_Eq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (BEq v1 a2) / st -->b (BEq v1 a2')
  | BS_Eq : forall st n1 n2,
      (BEq (ANum n1) (ANum n2)) / st -->b
      (if (n1 =? n2) then BTrue else BFalse)
  | BS_LtEq1 : forall st a1 a1' a2,
      a1 / st -->a a1' ->
      (BLe a1 a2) / st -->b (BLe a1' a2)
  | BS_LtEq2 : forall st v1 a2 a2',
      aval v1 ->
      a2 / st -->a a2' ->
      (BLe v1 a2) / st -->b (BLe v1 a2')
  | BS_LtEq : forall st n1 n2,
      (BLe (ANum n1) (ANum n2)) / st -->b
               (if (n1 <=? n2) then BTrue else BFalse)
  | BS_NotStep : forall st b1 b1',
      b1 / st -->b b1' ->
      (BNot b1) / st -->b (BNot b1')
  | BS_NotTrue : forall st,
      (BNot BTrue) / st -->b BFalse
  | BS_NotFalse : forall st,
      (BNot BFalse) / st -->b BTrue
  | BS_AndTrueStep : forall st b2 b2',
      b2 / st -->b b2' ->
      (BAnd BTrue b2) / st -->b (BAnd BTrue b2')
  | BS_AndStep : forall st b1 b1' b2,
      b1 / st -->b b1' ->
      (BAnd b1 b2) / st -->b (BAnd b1' b2)
  | BS_AndTrueTrue : forall st,
      (BAnd BTrue BTrue) / st -->b BTrue
  | BS_AndTrueFalse : forall st,
      (BAnd BTrue BFalse) / st -->b BFalse
  | BS_AndFalse : forall st b2,
      (BAnd BFalse b2) / st -->b BFalse

  where " t '/' st '-->b' t' " := (bstep st t t').


(* Small-step evaluation relation for commands *)
Inductive cstep : (com * state) -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st

  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).


Definition relation (X : Type) := X -> X -> Prop.

Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '/' st '-->*' t' '/' st' " :=
  (multi cstep (t, st) (t', st'))
  (at level 40, st at level 39, t' at level 39).

Example ex1 :
  <{if X = 1 then X := 2 else X := 1 end}> / (X !-> 1)
  -->*
  <{skip}> / (X !-> 2).
Proof.
    eapply multi_step.
    - apply CS_IfStep. apply BS_Eq1. apply AS_Id.
    - eapply multi_step.
      -- apply CS_IfStep. apply BS_Eq.
      -- simpl. eapply multi_step.
         --- apply CS_IfTrue.
         --- eapply multi_step.
            ---- apply CS_Asgn.
            ---- rewrite t_update_shadow. apply multi_refl.
Qed.

Example ex2 :
  <{X := 2}> / (X !-> 1)
  -->*
  <{skip}> / (X !-> 2).
Proof.
    eapply multi_step.
    - apply CS_Asgn.
    - rewrite t_update_shadow. apply multi_refl.
Qed.


Module CImp.

Inductive com : Type :=
  | CSkip : com
  | CAsgn : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com
  | CPar : com -> com -> com.

Notation "'par' c1 'with' c2 'end'" :=
         (CPar c1 c2)
            (in custom com at level 0, c1 at level 99, c2 at level 99).
Notation "'skip'"  :=
         CSkip (in custom com at level 0).
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity).
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity).
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99).
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99).

Inductive cstep : (com * state)  -> (com * state) -> Prop :=
  | CS_AsgnStep : forall st i a1 a1',
      a1 / st -->a a1' ->
      <{ i := a1 }> / st --> <{ i := a1' }> / st
  | CS_Asgn : forall st i (n : nat),
      <{ i := n }> / st --> <{ skip }> / (i !-> n ; st)
  | CS_SeqStep : forall st c1 c1' st' c2,
      c1 / st --> c1' / st' ->
      <{ c1 ; c2 }> / st --> <{ c1' ; c2 }> / st'
  | CS_SeqFinish : forall st c2,
      <{ skip ; c2 }> / st --> c2 / st
  | CS_IfStep : forall st b1 b1' c1 c2,
      b1 / st -->b b1' ->
      <{ if b1 then c1 else c2 end }> / st
      -->
      <{ if b1' then c1 else c2 end }> / st
  | CS_IfTrue : forall st c1 c2,
      <{ if true then c1 else c2 end }> / st --> c1 / st
  | CS_IfFalse : forall st c1 c2,
      <{ if false then c1 else c2 end }> / st --> c2 / st
  | CS_While : forall st b1 c1,
      <{ while b1 do c1 end }> / st
      -->
      <{ if b1 then c1; while b1 do c1 end else skip end }> / st
  | CS_Par1 : forall st c1 c1' c2 st',
      c1 / st --> c1' / st' ->
      <{par c1 with c2 end}> / st --> <{par c1' with c2 end}> / st'
  | CS_Par2 : forall st c1 c2 c2' st',
      c2 / st --> c2' / st' ->
      <{par c1 with c2 end}> / st --> <{par c1 with c2' end}> / st'
  | CS_ParDone : forall st,
      <{par skip with skip end}> / st --> <{skip}> / st
  where " t '/' st '-->' t' '/' st' " := (cstep (t,st) (t',st')).

End CImp.