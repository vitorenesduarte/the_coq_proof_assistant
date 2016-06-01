(* =========== Basic tactics :
-> intro - introduction rule for Pi;
-> apply - elimination rule for Pi;
-> assumption, exact - match conclusion with an hypothesis. 
*)

(* =========== Tactics for first-order reasoning:
-> intro - introduction rule for negation, implication and universal quantification
-> split - introduction rule for conjunction
-> left, right - introduction rule for disjuntion
-> exists x - introduction rule for existencial quantification
-> apply H -  elimination rule for negation, implication and universal quantification
-> elim H - elimination rule for conjunction, disjuntion and existencial quantification
-> destruct H as ... - elimination rule for: [H1 H2] conjunction, [H1 | H2] disjuntion, [x H] exists
*)

(* =========== Tactics for EQUALITY and REWRITING :
-> rewrite - rewrites an equality;
-> rewrite <- - reverse rewrite of an equality;
-> reflexivity - reflexivity property for equality;
-> symmetry - symmetry property for equality;
-> transitivity - transitivity property for equality.
*)

(* =========== Tactics for EVALUATION and CONVERTIBILITY :
-> simpl, red, cbv, lazy - performs evaluation;
-> pattern - performs a beta-expansion on the goal;
-> change - replaces the goal by a convertible one.
*)

(* =========== Tactics for INDUCTION :
-> elim - to apply the corresponding induction principle;
-> induction - performs induction on an identifier;
-> destruct - case analysis;
-> discriminate - discriminates objects built from different constructors;
-> injection - constructors of inductive types are injections; 
-> inversion - given an inductive type instance, find all the necessary condition 
               that must hold on the arguments of its constructors.
*)

(* =========== LIBRARIES 
A large base of definitions and facts found in the Coq Standard Library.
Often used libraries: 
-> Arith - unary integers;
-> ZArith - binary integers;
-> List - polymorphic lists;

Useful commands for finding theorems acting on a given identifier:
-> Search
-> SearchAbout
-> SearchPattern
*)

(* =========== AUTOMATISATION
For some specific domains, Coq is able to support some degree of automatisation:
-> auto - automatically applies theorems from a database;
-> tauto, intuition - decision procedures for specific classes of goals (e.g. propositional logic);
-> firstorder - useful to prove facts that are tautologies in intuitionistic FOL;
-> omega, ring - specialized tactics for numerical properties.
*)

(* =========== USEFUL tactics and commands...
Tactics:
-> clear - removes an hypothesis from the environment;
-> generalize - re-introduce an hypothesis into the goal;
-> cut, assert - proves the goal through an intermediate result;
-> pattern - performs eta-expansion on the goal.

Commands:
-> Admitted - aborts the current proof (property is assumed);
-> Set Implicit Arguments - makes possible to omit some arguments (when inferable by the system);
-> Open Scope - opens a syntax notation scope (constants, operators, etc.)

See the Reference Manual...
 *)


(* ================================================================== *)

Require Import Arith.

Set Implicit Arguments.

Section Parte1.
(* ****** Prove os lemas desta secção SEM usar táticas automáticas ****** *)

Variables A B : Prop.
Variable X : Set.
Variables P Q R W : X -> Prop.


Lemma questao1 : (A->B) -> ((A/\B) -> A) /\ (A -> (A/\B)).
Proof.
intro H1.
split.
intro H2.
destruct H2 as [H3 H4].
exact H3.
intro H2.
split.
exact H2.
apply H1.
exact H2.
Qed.


Lemma questao2 : ~A \/ ~B -> ~(A /\ B).
Proof.
intro H.
intro H2.
destruct H2 as [H3 H4].
destruct H as [H5 | H6].
apply H5.
exact H3.
apply H6.
exact H4.
Qed.

Lemma questao3 : (forall x y:X, (R y) -> (P x)) -> (exists y:X, (R y)) -> (forall x:X, (P x)).
Proof.
intros H1 H2.
intro x.
destruct H2 as [y H3].
apply H1 with (y := y).
exact H3.
Qed.


Lemma questao4 : (forall z:X, (P z)->(W z)) -> (exists x:X, (P x)/\(Q x)) -> (exists y:X, (W y)/\(Q y)).
Proof.
intros H1 H2.
destruct H2 as [x H3].
destruct H3 as [H4 H5].
exists x.
split.
apply H1.
exact H4.
exact H5.
Qed.

Lemma questao5 : forall (x y:nat), x+2=y -> y>x.
Proof.
intros.
induction H.
rewrite plus_n_O.
SearchPattern (_ + _ > _).
apply plus_gt_compat_l.
SearchPattern (_ > 0).
apply gt_Sn_O.
Qed.

End Parte1.

(* ================================================================== *)

Section Parte2.

Require Import List.
Require Import ZArith.

Open Scope Z_scope.


Fixpoint Elem (A:Type) (a : A) (l : list A) {struct l} : Prop :=
  match l with
  | nil => False
  | b :: m => b = a \/ Elem a m
  end.

Fixpoint count (z:Z) (l:list Z) {struct l} : nat :=
  match l with
  | nil => O      
  | (z' :: l') =>
      match Z_eq_dec z z' with
      | left _ => S (count z l')
      | right _ => count z l'
      end
  end.

Inductive Prefix (A:Type) : list A -> list A -> Prop :=
  | PreNil : forall (l:list A), Prefix nil l
  | PreCons : forall (x:A) (l1 l2:list A), Prefix l1 l2 -> Prefix (x::l1) (x::l2).


Inductive SubList (A:Type) : list A -> list A -> Prop :=
  | SLnil : forall (l:list A), SubList nil l
  | SLcons1 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList (x::l1) (x::l2)
  | SLcons2 : forall (x:A) (l1 l2:list A), SubList l1 l2 -> SubList l1 (x::l2).


Inductive Sorted : list Z -> Prop := 
  | sorted0 : Sorted nil 
  | sorted1 : forall z:Z, Sorted (z :: nil) 
  | sorted2 : forall (z1 z2:Z) (l:list Z), 
        z1 <= z2 -> Sorted (z2 :: l) -> Sorted (z1 :: z2 :: l). 



Lemma questao6 :  forall (x:Z) (l: list Z), Sorted (x::l) -> Sorted l.
Proof.
intros x l H.
induction l.
(* base *)
apply sorted0.
(* ind1 *)
inversion H.
exact H4.
Qed.

Lemma questao7 : forall (x y:Z) (l: list Z), ~(Elem x (y::l)) -> ~(Elem x l).
Proof.
intros x y l.
intro H.
intro H1.
apply H.
simpl.
right; assumption.
Qed.

                                                                  
Close Scope Z_scope.

Lemma questao8 : forall (x:Z) (l: list Z), (count x l) > O -> Elem x l.
Proof.
induction l.
(* base *)
simpl.
intro H.
inversion H.
(* ind *)
intro H.
simpl.
simpl in H.
destruct Z.eq_dec.
left.
symmetry; assumption.
right.
apply IHl; assumption.
Qed.


Lemma questao9 : forall (A:Type) (x:A) (l1 l2: list A), (Elem x l1) -> SubList l1 l2 -> Elem x l2.
Proof.
intros.
induction H0.
induction l.
exact H.
simpl.
right; assumption.
simpl.
simpl in H.
destruct H as [H1 | H2].
left; assumption.
right.
apply IHSubList; assumption.
simpl.
right.
apply IHSubList; assumption.
Qed.

End Parte2.





