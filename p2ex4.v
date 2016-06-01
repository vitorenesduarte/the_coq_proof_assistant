Require Import List.

Set Implicit Arguments.

Inductive Prefix (A:Type) : list A -> list A -> Prop :=
| PreNil : forall l:list A, Prefix nil l
| PreCons : forall (x:A) (l1 l2:list A), Prefix l1 l2 -> Prefix (x::l1) (x::l2).

Lemma Ex4A : forall (A:Type) (l1 l2:list A), Prefix l1 l2 -> length l1 <= length l2.
Proof.
induction l1.
(* base *)
intros.
simpl.
SearchPattern (0 <= _).
apply Le.le_0_n.
(* ind *)
intros.
induction H.
(* base *)
simpl.
apply Le.le_0_n.
(* ind *)
simpl.
SearchPattern (S _ <= S _).
apply Le.le_n_S.
assumption.
Qed.


Lemma Ex4B : forall (A B:Type) (f: A->B) (l1 l2:list A), Prefix l1 l2 -> Prefix (map f l1) (map f l2).
Proof.
induction l1.
(* base *)
simpl.
intros.
apply PreNil.
(* ind *)
intros.
induction H.
(* base *)
simpl.
apply PreNil.
(* ind *)
simpl.
apply PreCons.
assumption.
Qed.


Lemma Ex4C : forall (A:Type) (l1 l2:list A), Prefix l1 (l1++l2).
Proof.
induction l1.
(* base *)
intros.
simpl.
apply PreNil.
(* ind *)
intros.
apply PreCons.
apply IHl1. (* lol *)
Qed.


Lemma Ex4D : forall (A:Type) (l1 l2:list A) (x:A), Prefix l1 l2 -> In x l1 -> In x l2.
Proof.
Abort.


