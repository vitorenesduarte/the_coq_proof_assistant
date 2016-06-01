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
-> unfold \u2013 applies the delta rule for a transparent constant;
-> pattern - performs a beta-expansion on the goal;
-> change - replaces the goal by a convertible one.
*)

(* =========== Tactics for INDUCTION :
-> elim - to apply the corresponding induction principle;
-> induction - performs induction on an identifier;
-> destruct - performs case analysis;
-> discriminate - discriminates objects built from different constructors;
-> injection - constructors of inductive types are injections; 
-> inversion - given an inductive type instance, find all the necessary condition 
               that must hold on the arguments of its constructors.
-> constructor - applies the adequate constructor to a goal of an inductive type.
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

See the Reference Manual:

http://coq.inria.fr/refman/index.html

*)

(* ================================================================== *)
(* ================================================================== *)

Require Import Arith.

Set Implicit Arguments.

Section Part1.
(* prove os lemas desta sec\u00e7\u00e3o SEM usar t\u00e1ticas autom\u00e1ticas *)

Variables A B C D : Prop.
Variable X : Set.
Variables P Q R : X -> Prop.
Variable a : X.
Variable f : X->X.
Variable M : X->X->X->Prop.


Lemma ex1 : (A->B) /\ (C->D) -> (A/\C->B/\D).
Proof.
Qed.


Lemma ex2 : ~A \/ B -> (A -> B).
Proof.
Qed.

Lemma ex3 : (forall x:X, (M a x x)) -> (forall x y z:X, (M x y z)->(M (f x) y (f z))) -> (exists z:X, (M (f a) z (f (f a)))).
Proof.
Qed.


End Part1.


(* ================================================================== *)
Section Part2.

Variables A B : Type.

Inductive LAB : Type :=
   | null : LAB
   | consA : A -> LAB -> LAB
   | consB : B -> LAB -> LAB.

Fixpoint dropB (l:LAB) : LAB :=
   match l with
     | null => null
     | (consA h t) => (consA h (dropB t))
     | (consB h t) => t
   end.


Fixpoint cleanB (l:LAB) : LAB :=
   match l with
     | null => null
     | (consA h t) => consA h (cleanB t)
     | (consB h t) => (cleanB t)
   end.

Fixpoint lengthA (l:LAB) : nat :=
   match l with
     | null => O
     | (consA h t) => S (lengthA t)
     | (consB h t) => lengthA t
   end.

Fixpoint lengthB (l:LAB) : nat :=
   match l with
     | null => O
     | (consA h t) => lengthB t
     | (consB h t) => S (lengthB t)
   end.

Fixpoint lengthAB (l:LAB) : nat :=
   match l with
     | null => O
     | (consA h t) => S (lengthAB t)
     | (consB h t) => S (lengthAB t)
   end.

Inductive ElemB (x:B) : LAB -> Prop :=
     | el_head : forall l, ElemB x (consB x l)
     | el_tailA : forall y l, ElemB x l -> ElemB x (consA y l)
     | el_tailB : forall y l, ElemB x l -> ElemB x (consB y l).



Lemma cleanB_dropB : forall l, cleanB (dropB l) = cleanB l.
Proof.
Qed.


Lemma countA_countAB : forall l, lengthA l <= lengthAB l.
Proof.
Qed.

Lemma elemB_countB : forall l, (exists x, ElemB x l) -> lengthB l > 0.
Proof.
Qed.


End Part2.
