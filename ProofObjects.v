Set Warnings "-notation-overridden,-parsing".
From LF Require Export IndProp.

Print even.
(* ==>
  Inductive even : nat -> Prop :=
    | ev_0 : even 0
    | ev_SS : forall n, even n -> even (S (S n)).
*)


Theorem ev_4'' : even 4.
Proof.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_SS.
  Show Proof.
  apply ev_0.
  Show Proof.
Qed.

Definition ev_4''' : even 4 :=
  ev_SS 2 (ev_SS 0 ev_0).

Check (ev_SS 2 (ev_SS 0 ev_0)).

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n H. simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.

Definition ev_plus4' : forall n, even n -> 
                        even (4 + n) :=
  fun (n : nat) => fun (H : even n) =>
    ev_SS (S (S n)) (ev_SS n H).

Definition ev_plus4'' (n : nat) (H : even n)
                    : even (4 + n) :=
  ev_SS (S (S n)) (ev_SS n H).

Check ev_plus4''.
(* ===>
     : forall n : nat, even n -> even (4 + n) *)

(*
     ∀(x:nat), nat 
  =  ∀(_:nat), nat 
  =  nat → nat
*)

Definition ev_plus2 : Prop :=
  forall n, forall (E : even n), even (n + 2).

Definition ev_plus2' : Prop :=
  forall n, forall (_ : even n), even (n + 2).

Definition ev_plus2'' : Prop :=
  forall n, even n -> even (n + 2).

Definition add1 : nat -> nat.
intro n.
Show Proof.
apply S.
Show Proof.
apply n. Defined.

Print add1.

Module Props.

Module And.
Inductive and (P Q : Prop) : Prop :=
| conj : P -> Q -> and P Q.
End And.

Print prod.

Definition and_comm'_aux P Q (H : P /\ Q) : 
                          Q /\ P :=
  match H with
  | conj HP HQ => conj HQ HP
  end.

Lemma and_comm : forall P Q : Prop, 
        P /\ Q <-> Q /\ P.
Proof.
  intros P Q. split.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
  - intros [HP HQ]. split.
    + apply HQ.
    + apply HP.
Qed.

Print and_comm'_aux.

Definition and_comm' P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm'_aux P Q) (and_comm'_aux Q P).

Print and_comm'.

Definition conj_fact : forall P Q R, 
  P /\ Q -> Q /\ R -> P /\ R.
intros P Q R [H0 H1] [_ H2].
split. apply H0. apply H2.
Defined.

Module Or.
Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.
End Or.

Definition or_comm : forall P Q, 
  P \/ Q -> Q \/ P.
intros P Q [H0 | H1].
right. apply H0.
left. apply H1.
Defined.

Module Ex.
Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.
End Ex.

Check ex (fun n => even n).

Definition some_nat_is_even : exists n, 
  even n :=
  ex_intro even 4 (ev_SS 2 (ev_SS 0 ev_0)).

Check ex_intro even 4.
Check ev_SS 2 (ev_SS 0 ev_0).

Definition ex_ev_Sn : ex (fun n => even (S n)).
  exists 1. apply (ev_SS 0 ev_0). Defined.

Inductive True : Prop :=
  | I : True.

Inductive False : Prop := .

End Props.

Module MyEquality.
Inductive eq {X:Type} : X -> X -> Prop :=
| eq_refl : forall x, eq x x.
Notation "x == y" := (eq x y)
                    (at level 70, no associativity)
                    : type_scope.

Definition four' : 2 + 2 == 1 + 3 :=
  eq_refl 4.

Definition singleton : forall (X:Type) (x:X), 
  []++[x] == x::[] :=
  fun (X:Type) (x:X) => eq_refl [x].

Check singleton nat 2.

Lemma equality__leibniz_equality : forall (X : Type) (x y: X),
  x == y -> forall P:X -> Prop, P x -> P y.
Proof.
  intros. inversion H. rewrite <- H2.
  apply H0.
Qed.

Lemma leibniz_equality__equality : forall (X : Type) (x y: X),
  (forall P: X -> Prop, P x -> P y) -> x == y.
Proof.
  intros. apply H. apply eq_refl.
Qed.

End MyEquality.