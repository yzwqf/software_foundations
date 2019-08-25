Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
Import ListNotations.
From LF Require Import Maps.

Module AExp.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Fixpoint aeval (a : aexp) : nat :=
  match a with
  | ANum n => n
  | APlus a1 a2 => (aeval a1) + (aeval a2)
  | AMinus a1 a2 => (aeval a1) - (aeval a2)
  | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1:
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof. reflexivity. Qed.

Fixpoint beval (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval a1) =? (aeval a2)
  | BLe a1 a2 => (aeval a1) <=? (aeval a2)
  | BNot b1 => negb (beval b1)
  | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

Fixpoint optimize_0plus (a:aexp) : aexp :=
  match a with
  | ANum n => ANum n
  | APlus (ANum 0) e2 => optimize_0plus e2
  | APlus e1 e2 => APlus (optimize_0plus e1) (optimize_0plus e2)
  | AMinus e1 e2 => AMinus (optimize_0plus e1) (optimize_0plus e2)
  | AMult e1 e2 => AMult (optimize_0plus e1) (optimize_0plus e2)
  end.

Example test_optimize_0plus:
  optimize_0plus (APlus (ANum 2)
                        (APlus (ANum 0)
                               (APlus (ANum 0) (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_0plus_sound: forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a.
  - (* ANum *) reflexivity.
  - (* APlus *) destruct a1 eqn:Ea1.
    + (* a1 = ANum n *) destruct n eqn:En.
      * (* n = 0 *) simpl. apply IHa2.
      * (* n <> 0 *) simpl. rewrite IHa2. 
        reflexivity.
    + (* a1 = APlus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMinus a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
    + (* a1 = AMult a1_1 a1_2 *)
      simpl. simpl in IHa1. rewrite IHa1.
      rewrite IHa2. reflexivity.
  - (* AMinus *)
    simpl. rewrite IHa1. rewrite IHa2. 
    reflexivity.
  - (* AMult *)
    simpl. rewrite IHa1. rewrite IHa2. 
    reflexivity. 
Qed.

Theorem silly1 : forall ae, 
  aeval ae = aeval ae.
Proof. try reflexivity. 
(* This just does reflexivity. *) 
Qed.

Theorem silly2 : forall (P : Prop), P -> P.
Proof.
  intros P HP.
  try reflexivity. 
  (* Just reflexivity would have failed. *)
  apply HP.
Qed.

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
    (* Leaves two subgoals, which are discharged identically...  *)
    - (* n=0 *) simpl. reflexivity.
    - (* n=Sn' *) simpl. reflexivity.
Qed.
(* Before and After ';' Tactics *)
Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  (* destruct the current goal *)
  destruct n; simpl; reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a. induction a;
  (* Most cases follow directly by the IH... *)
  try (simpl; rewrite IHa1; rewrite IHa2; 
      reflexivity).
  try reflexivity.
  - destruct a1 eqn:Ea1;
    (* Again, most cases follow directly by the IH: *)
    try (simpl; simpl in IHa1; rewrite IHa1;
        rewrite IHa2; reflexivity).
    + destruct n eqn:En; simpl;
      rewrite IHa2; reflexivity. 
Qed.

Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.

Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.

Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) 
                 (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) 
                 (optimize_0plus a2)
  | BNot b1 => BNot (optimize_0plus_b b1)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1)
                  (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
Proof.
  intros. induction b;
  try (simpl; 
    repeat rewrite optimize_0plus_sound';
    reflexivity); simpl;
  [rewrite IHb | rewrite IHb1; rewrite IHb2];
  reflexivity.
Qed.

Tactic Notation "simpl_and_try" tactic(c) :=
  simpl;
  try c.

(* Usage: simpl_and_try reflexivity. *)

Example silly_presburger_example : forall m n o p,
  m + n <= n + o /\ o + 3 = p + 3 ->
  m <= p.
Proof.
  intros. omega.
Qed.

Module aevalR_first_try.
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat) :
      aevalR e1 n1 ->
      aevalR e2 n2 ->
      aevalR (AMult e1 e2) (n1 * n2).

Module TooHardToRead.
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum n :
      aevalR (ANum n) n
  | E_APlus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2: aexp) (n1 n2: nat)
      (H1 : aevalR e1 n1)
      (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).
End TooHardToRead.

Notation "e '\\' n"
         := (aevalR e n)
            (at level 50, left associativity)
         : type_scope.
End aevalR_first_try.

Reserved Notation "e '\\' n" (at level 90, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) : (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (AMult e1 e2) \\ (n1 * n2)
  where "e '\\' n" := (aevalR e n) : type_scope.

Theorem aeval_iff_aevalR : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  split.
  - intros H. induction H; simpl.
    + (* E_ANum *)
      reflexivity.
    + (* E_APlus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMinus *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
    + (* E_AMult *)
      rewrite IHaevalR1. rewrite IHaevalR2. reflexivity.
  - generalize dependent n. induction a;
    simpl; intros; subst.
    + apply E_ANum.
    + apply E_APlus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
    + (* AMinus *)
      apply E_AMinus.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
    + (* AMult *)
      apply E_AMult.
      apply IHa1. reflexivity.
      apply IHa2. reflexivity.
Qed.
 
Theorem aeval_iff_aevalR' : forall a n,
  (a \\ n) <-> aeval a = n.
Proof.
  split.
  - intros H; induction H; 
    try (subst; reflexivity).
  - generalize dependent n.
    induction a; simpl; intros; subst; 
    constructor; try apply IHa1; 
    try apply IHa2; reflexivity.
Qed.

Lemma aeval_a_aevalR : forall e,
  e \\ aeval e.
Proof.
  intros.
  apply aeval_iff_aevalR' with (a := e) (n := (aeval e)).
  reflexivity.
Qed.

Reserved Notation "e '//' n" 
  (at level 90, left associativity).
Inductive bevalR : bexp -> bool -> Prop :=
  | E_BTrue : BTrue // true
  | E_BFalse : BFalse // false
  | E_BEq (e1 e2 : aexp) (n1 n2 : nat) (b : bool):
      (e1 \\ n1) -> (e2 \\ n2) -> 
        b = (n1 =? n2) ->
          (BEq e1 e2) // b
  | E_BLe (e1 e2 : aexp) (n1 n2 : nat) (b : bool):
      (e1 \\ n1) -> (e2 \\ n2) -> 
        b = (n1 <=? n2) ->
          (BLe e1 e2) // b
  | E_BNot (e1 : bexp) (b : bool) :
      (e1 // b) -> (BNot e1) // (negb b) 
  | E_BAnd (e1 e2 : bexp) (b1 b2 : bool) :
      (e1 // b1) -> (e2 // b2) ->
        (BAnd e1 e2) // (b1 && b2)
  where "e '//' n" := (bevalR e n) : type_scope.

Lemma beval_iff_bevalR : forall b bv,
  bevalR b bv <-> beval b = bv.
Proof.
  split.
  - intros H. induction H; simpl; try reflexivity;
    try (apply aeval_iff_aevalR in H; 
         apply aeval_iff_aevalR in H0;
         subst; reflexivity).
    + rewrite IHbevalR. reflexivity.
    + rewrite IHbevalR1, IHbevalR2. reflexivity.
  - generalize dependent bv. 
    induction b; simpl; intros.
    + subst. constructor.
    + subst. constructor.
    + apply E_BEq with (n1 := aeval a1) (n2 := aeval a2).
      apply aeval_a_aevalR. apply aeval_a_aevalR. 
      rewrite H. reflexivity.
    + apply E_BLe with (n1 := aeval a1) (n2 := aeval a2).
      apply aeval_a_aevalR. apply aeval_a_aevalR. 
      rewrite H. reflexivity.
    + rewrite <- H. constructor.
      apply IHb. reflexivity.
    + rewrite <- H. constructor.
      apply IHb1. reflexivity. apply IHb2. reflexivity.
Qed.

End AExp.

Module aevalR_division.

Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp). (* <--- NEW *)

Reserved Notation "e '\\' n" (at level 90, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) : (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (AMult e1 e2) \\ (n1 * n2)
  | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 \\ n1) -> (a2 \\ n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) -> (ADiv a1 a2) \\ n3
  where "e '\\' n" := (aevalR e n) : type_scope.
End aevalR_division.

Module aevalR_extended.

Reserved Notation "e '\\' n" (at level 90, left associativity).
Inductive aexp : Type :=
  | AAny (* <--- NEW *)
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Reserved Notation "e '\\' n" (at level 90, left associativity).
Inductive aevalR : aexp -> nat -> Prop :=
  | E_Any (n : nat) :
      AAny \\ n (* <--- NEW *)
  | E_ANum (n : nat) : (ANum n) \\ n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (APlus e1 e2) \\ (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (AMinus e1 e2) \\ (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
      (e1 \\ n1) -> (e2 \\ n2) 
   -> (AMult e1 e2) \\ (n1 * n2)
  where "e '\\' n" := (aevalR e n) : type_scope.

End aevalR_extended.

Definition state := total_map nat.

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string) (* <--- NEW *)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Definition bool_to_bexp (b : bool) : bexp :=
  if b then BTrue else BFalse.
Coercion bool_to_bexp : bool >-> bexp.

Bind Scope imp_scope with aexp.
Bind Scope imp_scope with bexp.
Delimit Scope imp_scope with imp.

Notation "x + y" := (APlus x y) (at level 50, left associativity) : imp_scope.
Notation "x - y" := (AMinus x y) (at level 50, left associativity) : imp_scope.
Notation "x * y" := (AMult x y) (at level 40, left associativity) : imp_scope.
Notation "x ≤ y" := (BLe x y) (at level 70, no associativity) : imp_scope.
Notation "x = y" := (BEq x y) (at level 70, no associativity) : imp_scope.
Notation "x && y" := (BAnd x y) (at level 40, left associativity) : imp_scope.
Notation "'~' b" := (BNot b) (at level 75, right associativity) : imp_scope.

Definition example_aexp := (3 + (X * 2))%imp : aexp.
Definition example_bexp := (true && ~ (X ≤ 4))%imp : bexp.

Set Printing Coercions.

Print example_bexp.

Unset Printing Coercions.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => (aeval st a1) =? (aeval st a2)
  | BLe a1 a2 => (aeval st a1) <=? (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).
Notation "a '!->' x" := (t_update empty_st a x) (at level 100).

Example aexp1 :
    aeval (X !-> 5) (3 + (X * 2))%imp
  = 13.
Proof. reflexivity. Qed.

Example bexp1 :
    beval (X !-> 5) (true && ~(X ≤ 4))%imp
  = true.
Proof. reflexivity. Qed.

 Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Bind Scope imp_scope with com.
Notation "'SKIP'" :=
   CSkip : imp_scope.
Notation "x '::=' a" :=
  (CAss x a) (at level 60) : imp_scope.
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity) : imp_scope.
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity) : imp_scope.
Notation "'TEST' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity) : imp_scope.

Definition fact_in_coq : com :=
  (Z ::= X;;
  Y ::= 1;;
  WHILE ~(Z = 0) DO
    Y ::= Y * Z;;
    Z ::= Z - 1
  END)%imp.

Unset Printing Notations.
Print fact_in_coq.

Locate "&&".
Locate ";;".
Locate "WHILE".

Locate aexp.

Definition plus2 : com :=
  X ::= X + 2.
Definition XtimesYinZ : com :=
  Z ::= X * Y.
Definition subtract_slowly_body : com :=
  Z ::= Z - 1 ;;
  X ::= X - 1.

Definition subtract_slowly : com :=
  (WHILE ~(X = 0) DO
    subtract_slowly_body
  END)%imp.

Definition subtract_3_from_5_slowly : com :=
  X ::= 3 ;;
  Z ::= 5 ;;
  subtract_slowly.

Print subtract_slowly.

Definition loop : com :=
  WHILE true DO
    SKIP
  END.

Open Scope imp_scope.
Fixpoint ceval_fun_no_while (st : state) (c : com)
                          : state :=
  match c with
    | SKIP => st
    | x ::= a1 =>
        (x !-> (aeval st a1) ; st)
    | c1 ;; c2 =>
        let st' := ceval_fun_no_while st c1 in
          ceval_fun_no_while st' c2
    | TEST b THEN c1 ELSE c2 FI =>
        if (beval st b)
          then ceval_fun_no_while st c1
          else ceval_fun_no_while st c2
    | WHILE b DO c END =>
        st (* bogus *)
  end.
Close Scope imp_scope.

Reserved Notation "st '=[' c ']=>' st'"
                  (at level 40).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ SKIP ]=> st
  | E_Ass : forall st a1 n x,
      aeval st a1 = n ->
      st =[ x ::= a1 ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st =[ c1 ]=> st' ->
      st' =[ c2 ]=> st'' ->
      st =[ c1 ;; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ TEST b THEN c1 ELSE c2 FI ]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ WHILE b DO c END ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st =[ c ]=> st' ->
      st' =[ WHILE b DO c END ]=> st'' ->
      st =[ WHILE b DO c END ]=> st''
  where "st =[ c ]=> st'" := (ceval c st st').

Example ceval_example1:
  empty_st =[
     X ::= 2;;
     TEST X ≤ 1
       THEN Y ::= 3
       ELSE Z ::= 4
     FI
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_IfFalse. reflexivity.
    apply E_Ass. reflexivity.
Qed.

Example ceval_example2:
  empty_st =[
    X ::= 0;; Y ::= 1;; Z ::= 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Ass. reflexivity.
  - apply E_Seq with (Y !-> 1; X !-> 0);
    apply E_Ass; reflexivity.
Qed.

Definition pup_to_n : com :=
  (Y ::= 0;;
  WHILE ~ (X = 0) DO
    Y ::= X + Y ;;
    X ::= X - 1
   END) % imp.

Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  unfold pup_to_n.
  apply E_Seq with (Y !-> 0; X !-> 2).
  - apply E_Ass. reflexivity.
  - apply E_WhileTrue with (X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
    + reflexivity.
    + apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2);
      apply E_Ass; reflexivity.
    + apply E_WhileTrue with 
      (X !-> 0; Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2).
      * reflexivity.
      * apply E_Seq with 
          (Y !-> 3; X !-> 1; Y !-> 2; Y !-> 0; X !-> 2);
        apply E_Ass; reflexivity.
      * apply E_WhileFalse. reflexivity.
Qed.

Theorem ceval_deterministic: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - reflexivity.
  - reflexivity.
  - assert (st' = st'0) as EQ1.
    { apply IHE1_1; assumption. }
    subst st'0. apply IHE1_2. assumption.
  - apply IHE1, H6.
  - rewrite H in H5. discriminate H5.
  - rewrite H in H5. discriminate H5.
  - apply IHE1, H6.
  - reflexivity.
  - rewrite H in H2. discriminate H2.
  - rewrite H in H4. discriminate H4.
  - assert (st' = st'0) as EQ1.
    { apply IHE1_1, H3. }
    subst st'0. apply IHE1_2. assumption.
Qed.

Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros st n st' HX Heval.
  inversion Heval. subst. clear Heval. simpl.
  apply t_update_eq.
Qed.

Theorem loop_never_stops : forall st st',
  ~ (st =[ loop ]=> st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE true DO SKIP END)%imp as loopdef 
    eqn:Heqloopdef.
  induction contra; try inversion Heqloopdef.
  - rewrite H1 in H. simpl in H. discriminate H.
  - subst. apply IHcontra2. reflexivity.
Qed.

Open Scope imp_scope.
Fixpoint no_whiles (c : com) : bool :=
  match c with
  | SKIP =>
      true
  | _ ::= _ =>
      true
  | c1 ;; c2 =>
      andb (no_whiles c1) (no_whiles c2)
  | TEST _ THEN ct ELSE cf FI =>
      andb (no_whiles ct) (no_whiles cf)
  | WHILE _ DO _ END =>
      false
  end.
Close Scope imp_scope.

Inductive no_whilesR : com -> Prop :=
  | N_Skip : no_whilesR SKIP
  | N_Ass : forall x a,
      no_whilesR (x ::= a)
  | N_Seq : forall c1 c2,
      no_whilesR c1 -> no_whilesR c2 ->
      no_whilesR (c1 ;; c2)
  | N_Test : forall b c1 c2,
      no_whilesR c1 -> no_whilesR c2 ->
        no_whilesR (TEST b THEN c1 ELSE c2 FI).

Theorem no_whiles_eqv:
   forall c, no_whiles c = true <-> no_whilesR c.
Proof.
  split. 
  - intros. induction c;
    try (simpl in H; apply andb_true_iff in H as [H H0]);
    try constructor; try apply IHc1, H; try apply IHc2;
    try apply H0. inversion H.
  - intros H. induction c;
    try reflexivity; try inversion H;
    try (simpl; apply andb_true_iff; split);
    try apply IHc1, H2; try apply IHc2; try apply H3;
    try apply H4.
Qed.