Set Warnings "-notation-overridden,-parsing".
From LF Require Export Tactics.

Theorem app_assoc_destruct : forall X (l1 l2 l3: list X),
  (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof.
  intros.
  induction l1 as [|h t IHl'].
  - simpl. reflexivity.
  - simpl. rewrite IHl'. reflexivity.
Qed.

(* parameterized propositions *)
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

Lemma succ_inj : injective S.
Proof.
  intros n m H.
  injection H as H1.
  apply H1.
Qed.

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. 
  split.
  - apply HA.
  - apply HB.
Qed.

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  apply and_intro.
  - destruct n as [|n'].
    + reflexivity.
    + simpl in H. discriminate H.
  - destruct m as [|m'].
    + reflexivity.
    + rewrite -> plus_comm in H. simpl in H.
      discriminate H.
Qed.

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed. 

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP. 
Qed.

Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].
  apply HQ. 
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP. 
Qed.

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split.
  - split. apply HP. apply HQ.
  - apply HR.
Qed.

Lemma or_example : forall n m : nat, 
  n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn. reflexivity.
  - rewrite Hm. rewrite <- mult_n_O.
  reflexivity.
Qed.

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

Module MyNot.
Definition not (P:Prop) := P -> False.
Notation "~ x" := (not x) : type_scope.
Check not.
(* ===> Prop -> Prop *)
Notation "x <> y" := (~ (x = y)).
End MyNot.

(*  Latin ex falso quodlibet
  = from falsehood follows whatever you like
  = principle of explosion. *)
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P contra.
  destruct contra.
Qed.

Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  unfold not.
  intros.
  apply H in H0.
  destruct H0.
Qed.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. 
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~ P) -> Q.
Proof.
  intros P Q [HP HNA]. 
  unfold not in HNA.
  apply HNA in HP. destruct HP. 
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~ ~ P.
Proof.
  intros P H.
  unfold not. intros G.
  apply G. apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~ Q -> ~ P).
Proof.
  unfold not.
  intros P Q H0 H1 H2. apply H0 in H2.
  apply H1 in H2. destruct H2.
Qed.

Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~ P).
Proof.
  intros P.
  unfold not.
  intros [H0 H1].
  apply H1 in H0.
  apply H0.
Qed.

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    exfalso. (* <=== *)
    apply H. reflexivity.
  - (* b = false *) reflexivity.
Qed.

Lemma True_is_true : True.
Proof. apply I. Qed.

Module MyIff.
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).
Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.
End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB. 
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. discriminate H'.
Qed.

Theorem or_depend_on_each_left : forall P Q : Prop,
  P -> P \/ Q.
Proof. Admitted.

Theorem or_depend_on_each_right : forall P Q : Prop,
  Q -> P \/ Q.
Proof. Admitted.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. split.
  { intros [H0 | H1].
    { split.
      - apply or_depend_on_each_left. apply H0.
      - apply or_depend_on_each_left. apply H0.
    } 
    { split.
      - apply proj1 in H1. 
        apply or_depend_on_each_right.
        apply H1.
      - apply proj2 in H1. 
        apply or_depend_on_each_right.
        apply H1.
    }
  }
  {
    intros [[H0 | H1] [H2 | H3]]. left.
    - apply H0.
    - apply or_depend_on_each_left. apply H0.
    - apply or_depend_on_each_left. apply H2.
    - apply or_depend_on_each_right. 
      apply and_intro. apply H1. apply H3.
  }
Qed. 

From Coq Require Import Setoids.Setoid.

Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof. Admitted.

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof. Admitted.

Lemma mult_0 : forall n m, 
  n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc : forall P Q R : Prop, 
  P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

Lemma mult_0_3 : forall n m p, 
  n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. 
  rewrite or_assoc. reflexivity.
Qed.

Lemma apply_iff_example : forall n m : nat, 
  n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. 
  apply mult_0. apply H.
Qed.

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H.
  unfold not.
  (* intros [x1 Hx1] is OK, too. *)
  intros H0.
  destruct H0 as [x1 Hx1]. 
  apply Hx1 in H. destruct H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> 
    (exists x, P x) \/ (exists x, Q x).
Proof.
  intros. split.
  - intros [x [H0 | H1]]. 
    + left. exists x. apply H0.
    + right. exists x. apply H1.
  - intros [[x0 H0] | [x1 H1]].
    + exists x0. left. apply H0.
    + exists x1. right. apply H1.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity. 
  - exists 2. rewrite <- H. reflexivity.
Qed.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros. split.
  - induction l as [|x' l' IHl'].
    + simpl. apply ex_falso_quodlibet.
    + simpl. intros [H0 | H1]. 
      * exists x'. split. apply H0. 
        left. reflexivity.
      * apply IHl' in H1. destruct H1 as [x [H1 H2]].
        exists x. split. apply H1. right. apply H2.
  - induction l as [|x' l' IHl'].
    + intros [x [H0 H1]]. simpl. simpl in H1.
      apply H1.
    + intros H. simpl in H.
      destruct H as [x [H1 [H2 | H3]]].
      * simpl. left. rewrite -> H2.
        apply H1.
      * simpl. right. apply IHl'.
        exists x. split. apply H1. apply H3.
Qed.


Lemma In_app_iff : forall A l l' (a:A),
  In a (l ++ l') <-> In a l \/ In a l'. 
Proof.
  intros. split.
  - induction l as [|x' l'' IHl''].
    + simpl. intros H. right. apply H.
    + simpl. intros [H0 | H1]. 
      * left. left. apply H0.
      * apply or_assoc. right. 
        apply IHl''. apply H1.
  - induction l as [|x' l'' IHl''].
    + simpl. intros [H0 | H1]. 
      * apply ex_falso_quodlibet. apply H0.
      * apply H1.
    + simpl. intros [[H0 | H1] | H2].
      * left. apply H0.
      * right. apply IHl''. left. apply H1.
      * right. apply IHl''. right. apply H2.
Qed.

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x :: l' => P x /\ All P l'
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros. split.
  - intros H. induction l as [|x l' IHl'].
    + simpl. reflexivity.
    + simpl. split.
      * apply H. simpl. left. reflexivity.
      * apply IHl'. intros x0 H0.
        simpl in H. apply H. right. apply H0.
  - intros H. induction l as [|x l' IHl'].
    + simpl. intros x0 H0. 
      apply ex_falso_quodlibet. apply H0.
    + simpl. simpl in H. 
      destruct H as [H0 H1].
      intros x0 [H2 | H3].
      * rewrite <- H2. apply H0.
      * apply IHl'. apply H1. apply H3.
Qed.

Definition combine_odd_even (Podd Peven : nat -> Prop) : 
   nat -> Prop :=
  fun (n : nat) => if oddb n 
                   then Podd n 
                   else Peven n.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros.
  unfold combine_odd_even.
  destruct (oddb n) eqn:E1.
  - apply H. reflexivity.
  - apply H0. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  unfold combine_odd_even.
  intros. rewrite -> H0 in H. apply H.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  unfold combine_odd_even.
  intros. rewrite H0 in H. apply H.
Qed.

(* Use theorems AS Function !!! *)
Lemma plus_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite plus_comm.
  rewrite (plus_comm y z).
  reflexivity.
Qed.

Lemma in_not_nil :
  forall A (x : A) (l : list A), 
    In x l -> l <> [].
Proof.
  intros A x l H. unfold not. intro Hl. destruct l.
  - simpl in H. destruct H.
  - discriminate Hl.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, 
    In 42 l -> l <> [].
Proof.
  (* WORKED IN CLASS *)
  intros l H.
  Fail apply in_not_nil.
Abort.

Lemma in_not_nil_42_take2 :
  forall l : list nat, 
    In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.

(* apply ... in ... *)
Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.

(* Explicitly apply the lemma to the value for x. *)
Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

(* Explicitly apply the lemma to a hypothesis. *)
Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil _ _ _ H).
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(*
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l. 

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.

I don't know what it means yet.
*)
Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof. reflexivity. Qed.

Axiom functional_extensionality : forall {X Y: Type}
  {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

Print Assumptions function_equality_ex2.

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.
Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Axiom rev_append_aux : forall X (x : X) (l: list X),
  rev_append l [x] = rev_append l [ ] ++ [x].

Lemma tr_rev_correct : forall X, 
  @tr_rev X = @rev X.
Proof. 
  intros.
  apply functional_extensionality.
  intros l. induction l as [|x l' IHl'].
  - reflexivity.
  - unfold tr_rev. simpl. 
    rewrite <- IHl'. unfold tr_rev. 
    apply rev_append_aux.
Qed.

Example even_42_bool : evenb 42 = true.
Proof. reflexivity. Qed.

Example even_42_prop : exists k, 42 = double k.
Proof. exists 21. reflexivity. Qed.

Theorem evenb_double : forall k, 
  evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. rewrite plus_comm. simpl.
    rewrite <- IHk'. reflexivity.
Qed.

(* Originally in Basics.v *)
Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof. Admitted.

Axiom negb_axiom1 : forall (b : bool),
  negb b = true -> b = false.

Axiom negb_axiom2 : forall (b : bool),
  negb b = false -> b = true.

Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros. induction n as [|n' IHn'].
  - simpl. exists 0. reflexivity.
  - destruct (evenb (S n')) eqn:E1.
    + rewrite evenb_S in E1. 
      apply negb_axiom1 in E1.
      rewrite E1 in IHn'. 
      destruct IHn' as [k0 IHn'].
      exists (S k0). rewrite IHn'.
      unfold double. symmetry. simpl.
      rewrite plus_comm. simpl. reflexivity.
    + rewrite evenb_S in E1. 
      apply negb_axiom2 in E1.
      rewrite E1 in IHn'. 
      destruct IHn' as [k0 IHn'].
      rewrite IHn'. exists k0.
      reflexivity.
Qed.

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

Theorem eqb_refl : forall n,
  true = (n =? n).
Proof.
  intros. induction n as [|n' H].
  - simpl. reflexivity.
  - simpl. apply H.
Qed.

Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply eqb_true.
  - intros H. rewrite H. rewrite <- eqb_refl. reflexivity.
Qed.