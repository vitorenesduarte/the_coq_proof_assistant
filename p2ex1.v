
Require Import Arith.

Set Implicit Arguments.
Require Import List.
Require Import ZArith.


Fixpoint sum (l:list nat) {struct l} : nat :=
  match l with
  | nil => O      
  | b :: m => b + sum(m)
  end.


Inductive Prefix (A:Type) : list A -> list A -> Prop :=
  | PreNil : forall (l:list A), Prefix nil l
  | PreCons : forall (x:A) (l1 l2:list A), Prefix l1 l2 -> Prefix (x::l1) (x::l2).



Lemma Ex1A : forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
induction l1.
(* base *)
intro l2.
simpl.
reflexivity.
(* ind *)
simpl.
intro l2.
rewrite IHl1.
SearchRewrite (_ + _).
rewrite plus_assoc_reverse.
reflexivity.
Qed.


Lemma Ex1B : forall l, sum (rev l) = sum l.
Proof.
induction l.
(* base *)
simpl.
reflexivity.
(* ind *)
simpl.
rewrite Ex1A.
simpl.
rewrite IHl.
SearchRewrite (_ + 0).
rewrite plus_0_r.
SearchPattern (?x + ?y = ?y + ?x).
rewrite plus_comm.
reflexivity.
Qed.

Lemma Ex1C : forall l1 l2, Prefix l1 l2 -> sum l1 <= sum l2.
Proof.
induction l1.
(* base *)
intros l2 H.
simpl.
apply le_0_n.
(* ind *)
intros l2.
intro.
induction H.
simpl.
apply le_0_n.
simpl.
SearchPattern (?x + _ <= ?x + _).
apply plus_le_compat_l.
assumption.
Qed.s


