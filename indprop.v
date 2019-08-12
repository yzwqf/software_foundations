Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.
Require Coq.omega.Omega.

Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS (n : nat) (H : even n) : even (S (S n)).
(* equavlent
Inductive even' : nat -> Prop :=
  | ev_0' : even' 0
  | ev_SS' : forall n, even' n -> even' (S (S n)). 
*)

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

Check (ev_SS 2 (ev_SS 0 ev_0)).

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

Theorem double_axiom1 : forall n,
  double (S n) = S (S (double n)).
Proof.
  intros. unfold double. simpl.
  rewrite plus_comm. simpl. reflexivity.
Qed. 

Theorem ev_double : forall n,
  even (double n).
Proof.
  unfold double. intros.
  induction n as [|n' IHn'].
  - simpl. apply ev_0.
  - simpl. rewrite -> plus_comm. simpl.
    apply ev_SS. apply IHn'.
Qed.

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [|n' E'].
  - left. reflexivity.
  - right. exists n'. split. 
    reflexivity. apply E'.
Qed.

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
Proof.
 intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the E = ev_SS n' E' case now. *)
  apply E'.
Qed.

Theorem one_not_even : ~ even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
  intros H. inversion H. Qed.

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros n0 E0.
  inversion E0 as [|n1 E1].
  inversion E1 as [|n2 E2].
  apply E2.
Qed.

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros E. 
  inversion E. inversion H0.
  inversion H2.
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. 
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. 
Qed.

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E. inversion E as [|n' E'].
  - exists 0. reflexivity.
  - assert (I : (exists k', n' = double k')
            ->  (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k').
      rewrite <- double_axiom1. reflexivity. }
  apply I.
Abort.

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - exists 0. reflexivity.
  - destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k').
    rewrite double_axiom1. reflexivity.
Qed.

Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

Axiom plus_aux_axiom1 : forall n m,
  n + n + (m + m) = n + m + (n + m).

Theorem ev_sum : forall n m, 
  even n -> even m -> even (n + m).
Proof.
  intros. apply ev_even_iff.
  apply ev_even_iff in H.
  apply ev_even_iff in H0.
  destruct H0 as [k0 H0].
  destruct H as [k1 H1].
  rewrite H0. rewrite H1. exists (k1 + k0).
  unfold double. rewrite plus_aux_axiom1. 
  reflexivity.
Qed.

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

Theorem even'_ev : forall n,
  even' n <-> even n.
Proof.
  intros. split.
  - intros H. induction H.
    apply ev_0. apply ev_SS. apply ev_0.
    apply ev_sum. apply IHeven'1.
    apply IHeven'2.
  - intros E. induction E.
    apply even'_0. 
    assert (I : n+ 2 = S (S n)). 
    { rewrite plus_comm. simpl. reflexivity. }
    rewrite <- I. apply even'_sum. 
    apply IHE. apply even'_2.
Qed.

Axiom plus_and_diff : forall n m k,
  n + m = k -> n = k - m.

Axiom plus_and_diff2 : forall n m,
  n + n - (m + m) = n - m + (n - m).

Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros. apply ev_even_iff.
  apply ev_even_iff in H.
  apply ev_even_iff in H0.
  destruct H as [i Hi]. destruct H0 as [j Hj].
  rewrite Hj in Hi. rewrite plus_comm in Hi.
  apply plus_and_diff in Hi. rewrite Hi. 
  unfold double. exists (i - j).
  apply plus_and_diff2.
Qed.

Axiom plus_n_assoc : forall n m k,
  n - k + (m - k) = n - k + m - k.

Axiom plus_n_aux : forall i j n,
  i + i - n + (j + j) - n =
    i + j - n + (i + j - n).

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  intros. apply ev_even_iff.
  apply ev_even_iff in H. 
  apply ev_even_iff in H0.
  destruct H as [i Hi]. destruct H0 as [j Hj].
  exists (i + j - n). rewrite plus_comm in Hi.
  rewrite plus_comm in Hj. 
  apply plus_and_diff in Hi.
  apply plus_and_diff in Hj.
  rewrite Hi. rewrite Hj. 
  rewrite plus_n_assoc. unfold double.
  apply plus_n_aux.
Qed.

Module Playground.

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n. Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n. 
Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  intros H. inversion H. inversion H2.
Qed.

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n : even (S n) -> next_even n (S n)
  | ne_2 n (H : even (S (S n))) : next_even n (S (S n)).

Lemma le_trans : forall m n o, 
  m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H0 H1.
  destruct H0. apply H1. 
  induction H1.
  + apply le_S. apply H0.
  + apply le_S. apply IHle. 
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n as [|n' IHn'].
  apply le_n. apply le_S. apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  reflexivity. apply le_S. apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros. inversion H.
  - reflexivity. 
  - apply (le_trans n (S n) m).
    apply le_S. apply le_n. apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros. rewrite plus_comm. 
  induction b as [|b' IHb'].
  - simpl. reflexivity.
  - simpl. apply le_S. apply IHb'.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  unfold lt. intros.
  inversion H.
  - split. apply n_le_m__Sn_le_Sm. 
    apply le_plus_l. apply n_le_m__Sn_le_Sm. 
    rewrite plus_comm. apply le_plus_l.
  - split.
    + apply n_le_m__Sn_le_Sm. 
      rewrite <- H1 in H.
      apply Sn_le_Sm__n_le_m in H.
      apply (le_trans n1 (n1 + n2) m0).
      apply le_plus_l. apply H.
    + apply n_le_m__Sn_le_Sm.
      rewrite <- H1 in H.
      apply Sn_le_Sm__n_le_m in H.
      apply (le_trans n2 (n1 + n2) m0).
      rewrite plus_comm. apply le_plus_l. 
      apply H.
Qed. 

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt. intros. apply n_le_m__Sn_le_Sm.
  apply (le_trans n (S n) m).
  apply le_S. apply le_n. apply H.
Qed.

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros. generalize dependent n. 
  induction m as [|m' IHm'].
  - induction n as [|n' IHn'].
    + intros H. apply le_n.
    + intros H. simpl in H. discriminate H.
  - induction n as [|n' IHn'].
    + assert (I : S m' = 0 + S m').
      { reflexivity. } rewrite I. intros H.
      apply le_plus_l.
    + intros H. apply n_le_m__Sn_le_Sm.
      apply IHm'. simpl in H. apply H.
Qed.

Theorem leb_n_n : forall n,
  n <=? n = true.
Proof.
  intros. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. apply IHn'.
Qed. 

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros. generalize dependent n.
  induction m as [|m' IHm'].
  - intros n H. inversion H. reflexivity.
  - intros n H. inversion H. 
    simpl. apply leb_n_n. 
    induction n as [|n' IHn'].
    reflexivity. apply IHm'. 
    apply (le_trans n' (S n') m').
    apply le_S. apply le_n. apply H1.
Qed.

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> 
    m <=? o = true -> 
      n <=? o = true.
Proof.
  intros. apply leb_correct.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply (le_trans n m o). apply H. apply H0.
Qed.

Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split.
  apply leb_complete. apply leb_correct.
Qed.

Module R.

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

Theorem R_m_n_o : forall (m n o:nat),
  R m n o <-> m + n = o.
Proof.
  split.
  - intros. induction H. 
    + reflexivity.
    + rewrite plus_comm. rewrite <- plus_n_Sm.
      rewrite plus_comm. apply f_equal.
      apply IHR. 
    + rewrite <- plus_n_Sm.
      apply f_equal. apply IHR.
    + inversion IHR. 
      rewrite <- plus_n_Sm in H1.
      inversion H1. reflexivity.
    + rewrite plus_comm. apply IHR.
  - generalize n o. induction m.
    intros n0. induction n0.
  + intros. rewrite <- H. apply c1.
  + intros. simpl in H. destruct o0. 
    * inversion H.
    * apply c3. apply IHn0. inversion H. reflexivity.
  + intros n0. induction n0.
    * intros. destruct o0. inversion H.
      apply c2. inversion H. rewrite H1. apply IHm. apply H1.
    * intros. destruct o0. inversion H.
      destruct o0. inversion H. rewrite <- plus_n_Sm in H1.
      inversion H1.
      apply c2. apply c3. apply IHm.
      inversion H. rewrite <- plus_n_Sm in H1.
      inversion H1. reflexivity.
Qed.

End R.

Inductive subseq : list nat -> list nat -> Prop :=
  | sub_nil : forall l, subseq [] l
  | sub_one : forall n l1 l2, 
      subseq l1 l2 -> subseq l1 (n :: l2)
  | sub_two : forall n l1 l2, 
      subseq l1 l2 -> subseq (n :: l1) (n :: l2).

