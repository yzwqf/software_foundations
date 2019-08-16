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
    + simpl. apply f_equal. apply IHR.
    + rewrite <- plus_n_Sm. simpl. apply f_equal. apply IHR.
    + rewrite <- plus_n_Sm in IHR. simpl in IHR. injection IHR. 
      intros. apply H0.
    + rewrite plus_comm. apply IHR.
  -  generalize n o. induction m.
    + intros n0. induction n0.
      * simpl. intros. rewrite <- H. apply c1.
      * simpl. intros. rewrite <- H. apply c3. 
        apply IHn0 with (o := n0). simpl. reflexivity.
    + intros n0. induction n0.
      * simpl. intros. rewrite plus_comm in H. 
        simpl in H. rewrite <- H. apply c2.
        apply IHm. rewrite plus_comm. reflexivity.
      * simpl. rewrite plus_comm. simpl. intros.
        rewrite <- H. apply c3. apply IHn0.
        simpl. apply f_equal. rewrite plus_comm.
        reflexivity.
Qed. 

End R.

Inductive subseq : list nat -> list nat -> Prop :=
  | sub_nil : forall l, subseq [] l
  | sub_one : forall n l1 l2, 
      subseq l1 l2 -> subseq l1 (n :: l2)
  | sub_two : forall n l1 l2, 
      subseq l1 l2 -> subseq (n :: l1) (n :: l2).

Theorem subseq_refl : forall (l : list nat), 
  subseq l l.
Proof.
  intros. induction l as [|h t IHt].
  - apply sub_nil.
  - apply sub_two. apply IHt.
Qed.

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros. induction H.
  - apply sub_nil.
  - apply sub_one. apply IHsubseq.
  - apply sub_two. apply IHsubseq.
Qed. 

Theorem subseq_aux_0 : forall n (l1 l2:list nat),
  subseq (n :: l1) l2 -> subseq l1 l2.
Proof. 
  intros.
  induction l2.
  - inversion H.
  - apply sub_one. inversion H.
    + apply IHl2. apply H2.
    + apply H1.
Qed.

Theorem subseq_aux_1 : forall n (l1 l2 : list nat),
  subseq (n :: l1) (n :: l2) -> subseq l1 l2.
Proof.
  intros. inversion H.
  apply subseq_aux_0 in H2. apply H2.
  apply H1. 
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3. 
  generalize dependent l1.
  generalize dependent l2.
  generalize dependent l3.
  induction l3.
  - intros l2 l1 H0 H1. inversion H1.
    rewrite <- H in H0. apply H0.
  - intros l2 l1 H0 H1. inversion H1.
    + rewrite <- H in H0. inversion H0.
      apply sub_nil.
    + destruct H0 as [| h | h].
      * apply sub_nil.
      * apply sub_one. 
        apply IHl3 with (l2 := h :: l2).
        apply sub_one. apply H0. apply H3.
      * apply sub_one.
        apply IHl3 with (l2 := h :: l2).
        apply sub_two. apply H0. apply H3.
    + destruct H0 as [| h | h].
      * apply sub_nil.
      * apply sub_one.
        apply IHl3 with (l2 := l2).
        apply H0. injection H2. intros.
        rewrite H in H6. rewrite H6 in H1.
        apply subseq_aux_1 in H1. apply H1.
      * injection H2. intros. rewrite <- H6.
        rewrite H. apply sub_two. 
        apply IHl3 with (l2 := l2).
        apply H0. rewrite <- H in H1.
        rewrite H6 in H1. 
        apply subseq_aux_1 in H1.
        apply H1. 
Qed.

Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l, R n l -> R (S n) (n :: l)
  | c3 : forall n l, R (S n) l -> R n l.

(*
Provable:
   R 1 [1;2;1;0] 
Not provable:
   R 2 [1;0]
   R 6 [3;2;1;0]
*)

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

Inductive exp_match {T} : 
  list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

Notation "s =~ re" := (exp_match s re) (at level 80).

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

Lemma MStar1 : forall T s (re : @reg_exp T) ,
  s =~ re ->
  s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  apply H. apply MStar0.
Qed.

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s H. inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) 
                (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H0 | H1].
  apply MUnionL. apply H0.
  apply MUnionR. apply H1.
Qed.

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros.
  generalize dependent s1.
  induction s2. 
  - simpl. intros s1. split. 
    + intros H. inversion H. reflexivity.
    + intros. rewrite H. apply MEmpty.
  - split. 
    + intros H. inversion H. 
      inversion H3. simpl.
      apply f_equal. apply IHs2.
      apply H4.
    + intros H. rewrite H. simpl.
      apply (MApp [x] (Char x) s2 _).
      apply MChar. apply IHs2.
      reflexivity.
Qed.

Lemma MStar' : forall T (ss : list (list T)) 
              (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros. induction ss as [|s' ss' IHss'].
  - simpl. apply MStar0.
  - simpl. apply MStarApp. apply H. simpl.
    left. reflexivity. apply IHss'.
    intros s H1. apply H. simpl. right.
    apply H1.
Qed.

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin. 
  induction Hmatch as
  [| x'
   | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
   | s1 re1 re2 Hmatch IH
   | re1 s2 re2 Hmatch IH
   | re 
   | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - apply Hin.
  - apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + left. apply (IH1 Hin). 
    + right. apply (IH2 Hin).
  - simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - destruct Hin.
  - simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + apply (IH1 Hin).
    + apply (IH2 Hin).
Qed.

Theorem app_aux_1 : forall X (l1 l2 l3 : list X),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof. Admitted.

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.
  generalize dependent s2.
  induction H1
  as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
     |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
     |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].
  - (* MEmpty *) discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - injection Heqre'. 
    intros Heqre'' s H.
    apply H.
  - injection Heqre'. intros H0.
    intros s2 H1. rewrite app_aux_1.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2. rewrite H0. 
      reflexivity. apply H1.
Qed.

Fixpoint re_not_empty {T : Type} 
        (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char x => true
  | App re1 re2 => re_not_empty re1 
                && re_not_empty re2
  | Union re1 re2 => re_not_empty re1 
                || re_not_empty re2
  | Star re => true
  end.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) 
      <-> re_not_empty re = true.
Proof.
  intros. split.
  - intros H. destruct H as [s].
    induction H. reflexivity.
    reflexivity. simpl. 
    rewrite IHexp_match1.
    rewrite IHexp_match2. 
    reflexivity. simpl. 
    rewrite IHexp_match.
    reflexivity. simpl. 
    rewrite IHexp_match.
    apply orb_true_iff. 
    right. reflexivity.
    reflexivity. reflexivity.
  - intros H. induction re.
    + discriminate. 
    + exists []. apply MEmpty. 
    + exists [t]. apply MChar. 
    + simpl in H. apply andb_true_iff in H.
      destruct H as [H0 H1].
      destruct IHre1. apply H0.
      destruct IHre2. apply H1.  
      exists (x ++ x0). apply MApp.
      apply H. apply H2.
    + simpl in H. apply orb_true_iff in H.
      destruct H as [H0 | H1].
      * apply IHre1 in H0. destruct H0.
        exists x. apply MUnionL.
        apply H.
      * apply IHre2 in H1. destruct H1.
        exists x. apply MUnionR. 
        apply H.
    + exists []. apply MStar0.
Qed.  

(*
Lemma MStar' : forall T (ss : list (list T)) 
              (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros. remember (Star re) as re'.
  induction H.
  - discriminate.
  - (* MChar *) discriminate.
  - (* MApp *) discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.
  - exists []. split. reflexivity.
    simpl. intros s. 
    apply ex_falso_quodlibet.
  - exists [s1;s2]. split. simpl.
    rewrite app_nil_r. reflexivity.
    intros s' H1. unfold In in H1.
    injection Heqre'. intros H2.
    destruct H1 as [H1 | [H1 | H1]].
    + rewrite <- H1. rewrite <- H2.
      apply H.
    + rewrite <- H1. 
*)

Theorem app_aux_2 : forall X (l1 l2 l3 : list X),
  (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof. Admitted.

Module Pumping.
Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros. induction n as [|n IHn].
  reflexivity. simpl. rewrite IHn, app_aux_2. 
  reflexivity.
Qed.

(*
Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Import Coq.omega.Omega.
Proof.
  intros T re s Hmatch.
  induction Hmatch as
  [| x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  - simpl. omega.
  - simpl. omega.
  - simpl. intros H. 
Qed.
*)
End Pumping.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H : P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(* REWRITE'S EFFECT HERE IS MYSTERY *)
Theorem iff_reflect : forall P b, 
  (P <-> b = true) -> reflect P b.
Proof.
  intros P b H. destruct b.
  - apply ReflectT. apply H. reflexivity.
  - apply ReflectF. rewrite H. intros H'.
    discriminate.
Qed.

Theorem reflect_iff : forall P b, 
  reflect P b -> (P <-> b = true).
Proof.
  intros. unfold iff. destruct b.
  - split. intros H0. reflexivity.
    intros H0. inversion H. apply H1.
  - inversion H. unfold not in H0. 
    split. intros H1. apply H0 in H1.
    apply ex_falso_quodlibet, H1.
    intros H1. discriminate H1.
Qed.

Lemma eqbP : forall n m, 
  reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. 
  rewrite eqb_eq. reflexivity.
Qed.

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l =  *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) 
              + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~ (In n l).
Proof.
  intros. unfold not. 
  induction l as [|h t IHt].
  - apply ex_falso_quodlibet.
  - simpl. simpl in H. intros [H1 | H2]. 
    rewrite H1 in H. rewrite n_equal_to_n in H.
    discriminate H. apply IHt.
    destruct (eqbP n h). discriminate H.
    simpl in H. apply H. apply H2.
Qed.
