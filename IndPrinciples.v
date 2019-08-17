Set Warnings "-notation-overridden,-parsing".
From LF Require Export ProofObjects.

Check nat_ind.
(*  ===> nat_ind :
           forall P : nat -> Prop,
              P 0  ->
              (forall n : nat, P n -> P (S n))  ->
              forall n : nat, P n  *)

Theorem mult_0_r' : forall n:nat,
  n * 0 = 0.
Proof.
  apply nat_ind. reflexivity. simpl.
  intros n H. apply H.
Qed.

Theorem plus_one_r' : forall n:nat,
  n + 1 = S n.
Proof.
  apply nat_ind. reflexivity.
  intros n H. simpl. rewrite H. reflexivity.
Qed.

Inductive yesno : Type :=
  | yes
  | no.
Check yesno_ind.
(* ===> yesno_ind : forall P : yesno -> Prop,
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind.
(*
rgb_ind
     : forall P : rgb -> Prop,
       P red ->
       P green ->
       P blue -> forall r : rgb, P r
*)

Inductive natlist : Type :=
  | nnil
  | ncons (n : nat) (l : natlist).
Check natlist_ind.
(*
natlist_ind
     : forall P : natlist -> Prop,
       P nnil ->
       (forall (n : nat) (l : natlist),
        P l -> P (ncons n l)) ->
       forall n : natlist, P n
*)

(* They are different !!! *)
Inductive natlist1 : Type :=
  | nnil1
  | nsnoc1 (l : natlist1) (n : nat).
Check natlist1_ind.
(*
natlist1_ind
     : forall P : natlist1 -> Prop,
       P nnil1 ->
       (forall l : natlist1,
        P l -> forall n : nat, P (nsnoc1 l n)) ->
       forall n : natlist1, P n
*)

Inductive byntree : Type :=
 | bempty
 | bleaf (yn : yesno)
 | nbranch (yn : yesno) (t1 t2 : byntree).
Check byntree_ind.

Inductive ExSet : Type :=
| con1 (b : bool)
| con2 (n : nat) (e : ExSet).
Check ExSet_ind.

Check list_ind.
(*
Inductive list (X:Type) : Type :=
| nil : list X
| cons : X → list X → list X.

list_ind
     : forall (X : Type) (P : list X -> Prop),
       P [ ] ->
       (forall (x : X) (l : list X),
        P l -> P (x :: l)) ->
       forall l : list X, P l
*)

Inductive tree (X:Type) : Type :=
  | leaf (x : X)
  | node (t1 t2 : tree X).
Check tree_ind.

Inductive mytype (X : Type) : Type :=
  | constr1 (x : X)
  | constr2 (n : nat)
  | constr3 (m : mytype X) (n : nat).
Check mytype_ind.

Inductive foo (X Y : Type) : Type :=
  | bar (x : X)
  | baz (y : Y)
  | quux (f1 : nat -> foo X Y).
Check foo_ind.

Inductive foo' (X:Type) : Type :=
  | C1 (l : list X) (f : foo' X)
  | C2.
Check foo'_ind.

Definition P_m0r : nat -> Prop :=
  fun n => n * 0 = 0.

Theorem mult_0_r'' : forall n:nat,
  P_m0r n.
Proof.
  apply nat_ind. reflexivity.
  intros n H. unfold P_m0r in *. simpl.
  apply H.
Qed.

Definition P_pc : nat -> Prop :=
  fun n => forall m : nat, m + n = n + m.

Theorem plus_comm' : forall n : nat,
  P_pc n.
Proof.
  apply nat_ind. 
  - unfold P_pc. simpl. intros m.
    rewrite plus_comm. reflexivity.
  - intros n H. unfold P_pc in *. intros m.
    rewrite plus_comm. reflexivity.
Qed.

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS : forall n : nat, even n -> even (S (S n)).

Check even_ind.

Theorem ev_ev' : forall n, even n -> even' n.
Proof.
  apply even_ind.
  - (* ev_0 *)
    apply even'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (even'_sum 2 m).
    + apply even'_2.
    + apply IH.
Qed.

(*
Inductive le : nat -> nat -> Prop :=
     | le_n : forall n, le n n
     | le_S : forall n m, (le n m) -> (le n (S m)). 
Check le_ind.
le_ind
     : forall P : nat -> nat -> Prop,
       (forall n : nat, P n n) ->
       (forall n m : nat,
        le n m -> P n m -> P n (S m)) ->
       forall n n0 : nat, le n n0 -> P n n0
*)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S m (H : le n m) : le n (S m).
Check le_ind.
(*
le_ind
     : forall (n : nat) (P : nat -> Prop),
       P n ->
       (forall m : nat,
        le n m -> P m -> P (S m)) ->
       forall n0 : nat, le n n0 -> P n0
*)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

Check R_ind.
