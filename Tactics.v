Set Warnings "-notation-overridden,-parsing".
From LF Require Export Induction_structure.

(*
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

Arguments nil {X}.
Arguments cons {X} _ _.


Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
*)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m) ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. Qed.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) 
  -> oddb 3 = true
  -> evenb 4 = true.
Proof.
  intros eqa eqb.
  apply eqb.
Qed.

Theorem silly3_firsttry : forall (n : nat),
  true = (n =? 5) ->
  (S (S n)) =? 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl.
  apply H.
Qed.

Theorem app_nil_r : forall (X:Type), forall l:list X,
  app l nil = l.
Proof.
  intros X l. 
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_assoc : forall A (l m n : list A),
  app (app l m) n = app (app l m) n.
Proof. Admitted.

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (app l1 l2) = app (rev l2) (rev l1).
Proof. Admitted.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [|h t IHt].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr.
    rewrite -> IHt. reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' -> l' = rev l.
Proof.
  intros l l' H.
  rewrite <- rev_involutive.
  rewrite -> H.
  rewrite -> rev_involutive.
  rewrite -> rev_involutive. 
  reflexivity.
Qed.
  

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity. 
Qed.
  
Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2.
  reflexivity. 
Qed.

Theorem trans_eq_example2 : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1. apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
  m = (S o) ->
  (n + p) = m ->
  (n + p) = (S o).
Proof.
  intros n m o p eq1 eq2.
  rewrite -> eq2. apply eq1.
Qed.

Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H. intros Hnm. apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H.
  injection H. intros H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Theorem injection_ex2 : forall (n m : nat),
  [n] = [m] ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm. rewrite Hnm.
  reflexivity. 
Qed.

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  injection H2. intros H21 H22.
  rewrite -> H22.
  reflexivity.
Qed.

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - simpl. intros H. discriminate H.
Qed.

Theorem discriminate_ex1 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. 
Qed.

Theorem discriminate_ex2 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra. discriminate contra. 
Qed.

Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j.
  intros H.
  discriminate H.
Qed.

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. 
  intros A B f x y eq. 
  rewrite eq. reflexivity.
Qed.

Theorem S_inj : forall (n m : nat) (b : bool),
     (S n) =? (S m) = b ->
     n =? m = b.
Proof.
  intros n m b H. simpl in H. apply H. 
Qed. 

Theorem silly3' : forall (n : nat),
  (n =? 5 = true -> (S (S n)) =? 7 = true) ->
  true = (n =? 5) ->
  true = ((S (S n)) =? 7).
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. 
  induction n as [|n' IHn'].
  induction m as [|m' IHm'].
  - reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Definition double (n : nat) : nat := n + n.

Theorem plus_comm : forall n m,
   n + m = m + n.
Proof. Admitted.

Theorem plus_aux1 : forall n m,
  S n + S n = S m + S m 
    -> n + n = m + m.
Proof.
  intros n. induction n as [|n'].
  - intros m H. simpl in H.
    simpl. symmetry in H.
    rewrite -> plus_comm in H.
    simpl in H. injection H as H1.
    rewrite -> H1. reflexivity.
  - intros m H. simpl in H. 
    rewrite -> plus_comm in H. simpl in H.
    symmetry in H. rewrite -> plus_comm in H.
    simpl in H. injection H as H'.  
    rewrite -> H'. simpl. 
    rewrite -> plus_comm. simpl. reflexivity.  
Qed.

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].  
  - intros m H. simpl in H. 
    destruct m as [|m'].
    + reflexivity.
    + discriminate H. 
  - intros m H. destruct m as [|m'].
    + simpl. discriminate H.
    + apply f_equal. apply IHn'. 
      apply plus_aux1 in H. apply H.
Qed. 

(*
Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n']. 
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) simpl. intros m eq. 
    destruct m as [| m'] eqn:E.
    + simpl. discriminate eq.
    + apply f_equal. apply IHn'.  
      injection eq as goal. apply goal.
Qed.
*)

Theorem equal_if_succ_equal : forall n m,
  n = m -> S n = S m.
Proof. Admitted.

Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
  intros n. induction n as [| n'].  
  - intros m H. simpl in H.
    destruct m as [|m'].
    + reflexivity.
    + discriminate H.
  - simpl. intros m H.
    destruct m as [|m'].
    + discriminate H.
    + apply equal_if_succ_equal.
      apply IHn'. apply H.
Qed.

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  - simpl. intros eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros eq. destruct n as [| n'] eqn:E.
    + discriminate eq.
    + apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m'].
  -  simpl. intros n eq. destruct n as [| n'] eqn:E.
    + reflexivity.
    + discriminate eq.
  - intros n eq. destruct n as [| n'] eqn:E.
    + discriminate eq.
    + apply f_equal.
      injection eq as goal. 
      rewrite -> plus_comm in goal.
      simpl in goal. symmetry in goal. 
      rewrite -> plus_comm in goal.
      simpl in goal. injection goal as fuck.
      apply plus_n_n_injective in fuck.
      rewrite -> fuck. reflexivity.  
Qed.

Theorem eqb_id_true : forall x y,
  eqb_id x y = true -> x = y.
Proof.
  intros [m] [n]. simpl. intros H.
  assert (H' : m = n). { apply eqb_true. apply H. }
  rewrite H'. reflexivity.
Qed.

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|h l' IHl'].
  - intros n. simpl. reflexivity.
  - intros n H. destruct n as [|n'].
    + simpl. discriminate.
    + simpl. apply IHl'. simpl in H.
      injection H as H'.
      apply H'.
Qed.

Definition square n := n * n.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof. Admitted.

Theorem mult_distr : forall n m p : nat,
  m * p + n * p = (m + n) * p.
Proof. Admitted.

Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. 
    rewrite -> mult_distr. reflexivity.
Qed.

Lemma square_mult : forall n m, 
  square (n * m) = square n * square m. 
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
    { rewrite mult_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 5.

Fact silly_fact_1 : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  simpl.
  reflexivity.
Qed.

Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.
  
Fact silly_fact_2' : forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. 
Qed.

Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq. 
  destruct (n =? 3) eqn:E1.
  - apply eqb_true in E1. rewrite -> E1.
    reflexivity.
  - destruct (n =? 5) eqn:E2.
    + apply eqb_true in E2. rewrite -> E2.
      reflexivity.
    + discriminate eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  - destruct (f true) eqn:E1.
    + rewrite -> E1. apply E1.
    + destruct (f false) eqn:E2.
      apply E1. apply E2.
  - destruct (f false) eqn:E3.
    + destruct (f true) eqn:E4.
      apply E4. apply E3.
    + rewrite -> E3. apply E3.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
   intros X Y l. 
   induction l as [| [x y] l'].
   - simpl. intros l1 l2 H. injection H as H1 H2.
     rewrite <- H1. rewrite <- H2. reflexivity.
   - intros l1 l2. simpl.
     destruct (split l').
     destruct l1.
     + intros H. inversion H. 
     + destruct l2.
       intros h. inversion h.
       intros h. inversion h. 
       simpl. rewrite -> IHl'. reflexivity.
       rewrite -> H1. rewrite -> H3. reflexivity.
Qed.

Theorem n_equal_to_n : forall (n : nat),
   n =? n = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p H1 H2.
  apply eqb_true in H1.
  apply eqb_true in H2.
  rewrite H1. rewrite <- H2.
  apply n_equal_to_n.
Qed.

Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - intros m. destruct m.
    + reflexivity.
    + simpl. reflexivity.
  - intros m. destruct m.
    + simpl. reflexivity.
    + simpl. apply IHn'.
Qed.

Definition split_combine_statement : Prop
  (* (": Prop" means that we are giving a name to a
     logical proposition here.) *)
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
Theorem split_combine : split_combine_statement.
Proof.
(* FILL IN HERE *) Admitted.
(* Do not modify the following line: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | h :: t => if (test h) then forallb test t else false
  end.

Example test_forallb_1 : forallb oddb [1;3;5;7;9] = true.
Proof. reflexivity. Qed.
Example test_forallb_2 : forallb negb [false;false] = true.
Proof. reflexivity. Qed.
Example test_forallb_3 : forallb evenb [0;2;4;5] = false.
Proof. reflexivity. Qed.
Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => false
  | h :: t => if (test h) then true else
              existsb test t
  end.

Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3 : existsb oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun y => negb (test y)) l).

Example test_existsb_1' : existsb' (eqb 5) [0;2;3;6] = false.
Proof. reflexivity. Qed.
Example test_existsb_2' : existsb' (andb true) [true;true;false] = true.
Proof. reflexivity. Qed.
Example test_existsb_3' : existsb' oddb [1;0;0;0;0;3] = true.
Proof. reflexivity. Qed.
Example test_existsb_4' : existsb' evenb [] = false.
Proof. reflexivity. Qed.

Theorem existsb_existsb' : forall (X : Type) (test : X -> bool) (l : list X),
  existsb test l = existsb' test l.
Proof.
  intros X test l.
  unfold existsb'.
  induction l as [|h t IHl'].
  - reflexivity.
  - simpl. destruct (test h).
    + symmetry. simpl. reflexivity.
    + symmetry. simpl. rewrite <- IHl'.
      reflexivity.
Qed.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true. 
Proof.
  intros X test x l.
  generalize dependent x.
  induction l as [|h t IHl'].
  - intros x lf H. discriminate H.
  - intros x lf H. simpl in H.  
    destruct (test h) eqn:E1.
    + injection H as H1 H2. rewrite <- H1.
      apply E1.
    + apply IHl' in H. apply H.
Qed.


  