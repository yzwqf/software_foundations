Inductive bit : Type :=
  | B0
  | B1.
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Definition all_zero (nb : nybble) : bool :=
  match nb with
    | (bits B0 B0 B0 B0) => true
    | (bits _ _ _ _) => false
  end.

Check (all_zero (bits B1 B0 B1 B0)).

Check (S (S (S (S O)))).

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n:nat) : bool := negb (evenb n).
Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Compute (plus 3 2).

(*  plus (S (S (S O))) (S (S O))
==> S (plus (S (S O)) (S (S O)))
      by the second clause of the match
==> S (S (plus (S O) (S (S O))))
      by the second clause of the match
==> S (S (S (plus O (S (S O)))))
      by the second clause of the match
==> S (S (S (S (S O))))
      by the first clause of the match
*)

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | 0, _ => 0
  | S _, 0 => n
  | S n', S m' => minus n' m'
  end.

Notation "x - y" := (minus x y)
                      (at level 50, left associativity)
                      : nat_scope.

Compute (10 - 8).

Fixpoint leb (n m : nat) : bool :=
  match n with
  | 0 => true
  | S n' =>
    match m with 
    | 0 => false
    | S m' => leb n' m'
    end
  end.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

Theorem plus_0_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  intros m n.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_0_n.
  reflexivity. Qed.

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. 
  destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [| n'].
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros [] [].
    - reflexivity.
    - simpl. intros H. rewrite -> H. reflexivity.
    - simpl. intros H. rewrite <- H. reflexivity.
    - simpl. intros H. rewrite <- H. reflexivity.
Qed.

(*
(false && false)%bool = true -> false = true

false = true -> false = true

H : false = true
______________________________________(1/1)
false = true

false = false
*)

Theorem identity_fn_applied_twice : 
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem negation_fn_applied_twice : 
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros.
  rewrite -> H.
  rewrite -> H.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_eq_orb : forall (b c : bool),
  (andb b c = orb b c) -> b = c.
Proof.
  intros [] [].
  - reflexivity.
  - simpl. intros H. rewrite <- H. reflexivity.
  - simpl. intros H. rewrite <- H. reflexivity.
  - simpl. intros H. reflexivity.
Qed.

Inductive bin : Type :=
  | Z
  | A (n : bin)
  | B (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B Z
  | B m' => A (incr m')
  | A m' => B m'  
  end.

Compute (incr (incr (A (B (B Z))))).

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => 0
  | B m' => S (2 * (bin_to_nat m'))
  | A m' => 2 * (bin_to_nat m')
  end.

Compute (bin_to_nat (incr (incr (A (B (B Z)))))).

Theorem plus_n_0 : forall n : nat, n = n + 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. 
Qed.

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

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

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. 
  induction n as [|n' IHn'].
  { induction m as [|m' IHm'].
    - reflexivity.
    - simpl. rewrite <- plus_n_0. reflexivity. } 
  { simpl. rewrite -> IHn'. induction m as [|m' IHm'].
    - simpl. reflexivity.  
    - simpl. rewrite -> plus_n_Sm. reflexivity. }
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'.
    rewrite -> plus_n_Sm. 
    reflexivity.
Qed.

Theorem negation_applied_twice: forall x : bool,
  negb (negb x) = x.
Proof.
  intros [].
  - reflexivity.
  - reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - rewrite -> IHn'.
    rewrite -> negation_applied_twice.
    reflexivity.
Qed.

Theorem mult_0_plus_2' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. Qed.

Inductive natprod : Type :=
| pair (n1 n2 : nat).

Notation "( x , y )" := (pair x y).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst' p, snd' p).
Proof.
  intros p. destruct p as [n m]. 
  simpl. reflexivity. 
Qed.

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd' p, fst' p) = swap_pair p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd : forall (p : natprod),
  fst' (swap_pair p) = snd' p.
Proof.
  intros p. destruct p as [n m].
  simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "[]" := nil.

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end. 

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t =>
    match h with
    | 0 => nonzeros t
    | (S n) => (S n) :: (nonzeros t)
    end
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint oddmembers (l:natlist) : natlist := 
  match l with
  | nil => nil
  | h :: t =>
    match (oddb h) with
    | false => oddmembers t
    | true => h :: (oddmembers t)
    end
  end.

Example test_oddmembers:
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
   (length (oddmembers l)).

Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t =>
    match l2 with 
    | nil => h :: t
    | h2 :: t2 => h :: h2 :: alternate t t2
    end
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
    match (h =? v) with
    | false => count v t
    | true => S (count v t)
    end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

Definition sum (s:bag) (b:bag) : bag :=
  s ++ b.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag := 
  v :: s.

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  negb ((count v s) =? 0).

Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  match s with
  | nil => nil
  | h :: t =>
    match (h =? v) with
    | false => h :: (remove_one v t)
    | true => t
    end
  end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag := 
  match s with
  | nil => nil
  | h :: t =>
    match (h =? v) with
    | false => h :: (remove_all v t)
    | true => remove_all v t
    end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool := 
  match s1 with 
  | nil => true
  | h :: t =>
    match (member h s2) with 
    | false => false
    | true => subset t (remove_one h s2)
    end
  end.

Example test_subset1: subset [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_subset2: subset [1;2;2] [2;1;4;1] = false.  
Proof. reflexivity. Qed.

Theorem n_equal_to_n : forall (n : nat),
   n =? n = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem bag_theorem : forall (n:nat) (b:bag), 
  count n (add n b) =? 0 = false.
Proof.
  intros n b.
  simpl.
  rewrite -> n_equal_to_n.
  simpl. reflexivity.
Qed.
  
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite -> IHl1'. reflexivity. Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl. rewrite -> app_length, plus_comm. 
    simpl. rewrite -> IHl'. reflexivity. Qed.

Search add.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [|n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> IHl'. reflexivity.
Qed.

Theorem app_assoc_destruct : forall l1 l2 l3: natlist,
  (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3.
Proof.
  Admitted.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1. 
Proof.
  intros l1 l2.
  induction l1 as [|n l1' IHl1'].
  { induction l2 as [|m l2' IHl2'].
    - reflexivity.
    - simpl. rewrite -> app_assoc. 
      rewrite -> app_nil_r. reflexivity. }
  { induction l2 as [|m l2' IHl2'].
    - simpl. rewrite -> app_nil_r.
      reflexivity.
    - simpl. rewrite -> IHl1'. simpl. 
      rewrite -> app_assoc_destruct. reflexivity. }
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. 
    rewrite -> IHl'. 
    reflexivity. 
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite <- app_assoc.
  rewrite <- app_assoc.
  reflexivity.
Qed.

(*
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b. *)

Theorem app_cons_assoc : forall l1 l2 : natlist, forall n : nat, 
    (n :: l1) ++ l2 = n :: (l1 ++ l2).
Proof.
  Admitted.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [|n l1' IHl1'].
  induction l2 as [|m l2' IHl2'].
  { reflexivity. }
  { destruct m as [|m'].
    reflexivity. reflexivity.
  }
  { destruct n as [|n']. 
    - simpl. rewrite -> IHl1'. reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity. 
  }
Qed.

Fixpoint eqblist (l1 l2 : natlist) : bool :=
  match l1, l2 with 
  | nil, nil => true
  | h :: t, nil => false
  | nil, h :: t => false
  | h :: t, r :: k =>
    match (h =? r) with
    | true => eqblist t k
    | false => false
    end
  end.

Example test_eqblist1 :
  (eqblist nil nil = true).
Proof. reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof. reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof. reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
  intros l.
  induction l as [|n l' IHl'].
  - reflexivity.
  - simpl. rewrite -> n_equal_to_n.
    rewrite <- IHl'.
    reflexivity.
Qed.

Theorem count_member_nonzero : forall (s : bag),
  1 <=? (count 1 (1 :: s)) = true.
Proof.
  intros s.
  induction s as [|n s' IHs'].
  - reflexivity.
  - reflexivity.
Qed.

Theorem leb_n_Sn : forall n,
  n <=? (S n) = true.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* 0 *)
    simpl. reflexivity.
  - (* S n' *)
    simpl. rewrite IHn'. reflexivity. 
Qed.

Theorem remove_does_not_increase_count: forall (s : bag),
  (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
Proof.
  intros s.
  induction s as [|n s' IHs'].
  { reflexivity. }
  { destruct n as [|n']. 
    - simpl. rewrite -> leb_n_Sn. reflexivity. 
    - simpl. rewrite -> IHs'. reflexivity. } 
Qed.

Theorem bag_count_sum : forall (s b : bag),
  (count 0 s) + (count 0 b) = count 0 (sum s b).
Proof.
  intros s b.
  induction s as [|n s' IHs'].
  induction b as [|m b' IHb'].
  { reflexivity. }
  { destruct m as [|m']. simpl.
    reflexivity. reflexivity. }
  { destruct n as [|n']. simpl. 
    - rewrite -> IHs'. reflexivity. 
    - simpl. rewrite -> IHs'. reflexivity. }   
Qed.

Theorem rev_injective : forall (l a : natlist),
  rev l = rev a -> l = a.
Proof.
  intros.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Fixpoint nth_error (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => match n =? O with
               | true => Some a
               | false => nth_error l' (pred n)
               end
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [4;5;6;7] 3 = Some 7.
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [4;5;6;7] 9 = None.
Proof. reflexivity. Qed.

Fixpoint nth_error' (l:natlist) (n:nat) : natoption :=
  match l with
  | nil => None
  | a :: l' => if n =? O then Some a
               else nth_error' l' (pred n)
  end.
 
Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

Definition hd_error (l : natlist) : natoption :=
  match l with
  | nil => None
  | h :: t => Some h
  end.

Example test_hd_error1 : hd_error [] = None.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error3 : hd_error [5;6] = Some 5.
Proof. reflexivity. Qed.

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim default (hd_error l).
Proof.
  intros l.
  destruct l as [|n l'].
  - reflexivity.
  - simpl. reflexivity.
Qed.

Inductive id : Type :=
  | Id (n : nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Theorem eqb_id_refl : forall x, 
  true = eqb_id x x.
Proof.
  intros x. destruct x as [m].
  simpl. rewrite -> n_equal_to_n.
  reflexivity.
Qed.

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.

 Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty => None
  | record y v d' => if eqb_id x y
                     then Some v
                     else find x d'
  end.

Theorem update_eq :
  forall (d : partial_map) (x : id) (v: nat),
    find x (update d x v) = Some v.
Proof.
  intros.
  simpl. rewrite <- eqb_id_refl. reflexivity.
Qed.

Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).