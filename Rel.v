Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Definition relation (X: Type) := X -> X -> Prop.

Print le.
(* ====> Inductive le (n : nat) : nat -> Prop :=
             le_n : n <= n
           | le_S : forall m : nat, n <= m -> n <= S m *)
Check le : nat -> nat -> Prop.
Check le : relation nat.

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, 
    R x y1 -> R x y2 -> y1 = y2.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense. {
    apply Hc with (x := 0).
    - apply le_n.
    - apply le_S. apply le_n. }
  discriminate Nonsense. 
Qed.

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.
Qed.

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, 
    (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  - (* le_n *) apply Hnm.
  - (* le_S *) apply le_S. apply IHHmo. 
Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. 
Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [|m' Hm'o].
  - apply le_S in Hnm. apply Hnm.
  - apply le_S, IHHm'o.
Qed.

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  - inversion Hmo.
  - apply Sn_le_Sm__n_le_m in Hmo.
    apply le_S in Hmo.
    apply (le_trans (S n) m (S o')).
    apply Hnm. apply Hmo.
Qed.

Theorem le_Sn_le : forall n m, 
  S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  apply le_S, le_n. apply H.
Qed.

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  intros n m H. inversion H. apply le_n. 
  apply le_Sn_le in H1. apply H1.
Qed.

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  unfold not. intros. induction n.
  inversion H. apply le_S_n in H. 
  apply IHn in H. apply H.
Qed.

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold symmetric. intros H.
  assert (1 <= 0) as Nonsense. 
  { apply H. apply le_S. apply le_n. }
  inversion Nonsense.
Qed.

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric. intros.
  inversion H. reflexivity.
  assert (S a <= a) as Nonsense.
  (* S b <= S a <= b *)
  { apply le_trans with (b := b).
  rewrite <- H2. apply le_n_S, H1. apply H0. }
  apply le_Sn_n in Nonsense.
  apply ex_falso_quodlibet, Nonsense.
Qed.

Theorem le_step : forall n m p,
  n < m -> m <= S p -> n <= p.
Proof.
  unfold lt. intros.
  apply le_S_n, (le_trans (S n) m (S p)).
  apply H. apply H0.
Qed.

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(* Actually, it is Partial Orders *)
Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ 
    (antisymmetric R) /\ (transitive R).

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
  - apply le_reflexive.
  - split.
    + apply le_antisymmetric.
    + apply le_trans.
Qed.

Inductive clos_refl_trans {A: Type} (R: relation A) : 
  relation A :=
    | rt_step x y (H : R x y) : clos_refl_trans R x y
    | rt_refl x : clos_refl_trans R x x
    | rt_trans x y z
          (Hxy : clos_refl_trans R x y)
          (Hyz : clos_refl_trans R y z) :
          clos_refl_trans R x z.

Print next_nat.
(*
Inductive next_nat : nat -> nat -> Prop :=
    nn : forall n : nat, next_nat n (S n)
*)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_trans with m. apply IHle.
      apply rt_step. apply nn.
  - intros H. induction H.
    + inversion H. apply le_S, le_n.
    + apply le_n.
    + apply le_trans with y. 
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2.
Qed.

Inductive clos_refl_trans_1n {A : Type}
                       (R : relation A) (x : A)
                             : A -> Prop :=
  | rt1n_refl : clos_refl_trans_1n R x x
  | rt1n_trans (y z : A)
      (Hxy : R x y) (Hrest : clos_refl_trans_1n R y z) :
      clos_refl_trans_1n R x z.

Lemma rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> clos_refl_trans_1n R x y.
Proof.
  intros X R x y H.
  apply rt1n_trans with y. 
  apply H. apply rt1n_refl.
Qed.

Lemma rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      clos_refl_trans_1n R x y ->
      clos_refl_trans_1n R y z ->
      clos_refl_trans_1n R x z.
Proof.
  intros. induction H.
  - apply H0.
  - apply rt1n_trans with y. apply Hxy.
    apply IHclos_refl_trans_1n, H0.
Qed.

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <->
    clos_refl_trans_1n R x y.
Proof.
  intros. split.
  - intros H. induction H.
    + apply rsc_R, H.
    + apply rt1n_refl.
    + apply rsc_trans with y.
      apply IHclos_refl_trans1. 
      apply IHclos_refl_trans2.
  - intros H. induction H.
    + apply rt_refl.
    + apply rt_trans with y. 
      apply rt_step in Hxy. apply Hxy.
      apply IHclos_refl_trans_1n.
Qed.