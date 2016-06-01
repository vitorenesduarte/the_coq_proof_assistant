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
(* =============== Reasoning about naturals and lists =============== *)
(* ================================================================== *)

Require Import List.

Set Implicit Arguments.

Print list.
Print app.

Locate "::".
Locate "++".


(* three similar proofs by induction using different tactics *)

Theorem app_l_nil : forall (A:Set) (l:list A), app l nil = l.
Proof.
intro A.
intro l.
SearchRewrite (_ ++ nil).
rewrite app_nil_r.
reflexivity.
Qed.

Theorem app_l_nil' : forall (A:Set) (l:list A), app l nil = l.
Proof.
intros A l.
pattern l.
apply list_ind.
(* base *)
rewrite app_nil_r.
reflexivity.
(* ind *)
intros a l0.
intro H1.
simpl.
rewrite H1.
reflexivity.
Qed.

Theorem app_l_nil'' : forall (A:Set) (l:list A), app l nil = l.
Proof.
induction l.
(* base *)
reflexivity.
(* ind *)
simpl.
rewrite IHl.
reflexivity.
Qed.


Print nat.
Print length.


(* 
 Exercise: prove that the length of the append of two lists is equal 
           to the addition of the length of each list 

*)

Lemma app_length : forall (A:Set) (l1 l2:list A), 
                    length (app l1 l2) = length l1 + length l2.
Proof.
intros A l1 l2.
induction l1.
(* base *)
simpl.
reflexivity.
simpl.
rewrite IHl1.
reflexivity.
Qed.

Fixpoint snoc (A:Type) (a:A) (l:list A) {struct l} : list A :=
    match l with
      | nil => a::nil
      | x::xs => x::(snoc a xs)
    end.


Lemma snoc_len : forall (A:Set) (a:A) (l:list A), length (snoc a l) =  1 + (length l).
Proof.
induction l.
(* base *)
simpl.
reflexivity.
(* ind *)
simpl.
rewrite IHl.
reflexivity.
Qed.

Lemma snoc_app : forall (A:Set) (a:A) (l:list A), snoc a l =  l ++ (a::nil).
Proof.
induction l.
(* base *)
simpl.
reflexivity.
(* ind *)
simpl.
rewrite IHl.
reflexivity.
Qed.

(* A predicate defined inductively *)

Fixpoint In (A:Set) (a:A) (l:list A) {struct l} : Prop :=
    match l with
      | nil => False
      | cons x xs => x = a \/ In a xs
    end.


Lemma in_app : forall (A:Set) (l1 l2:list A) (a:A), 
                           In a (app l1 l2) -> In a l1 \/ In a l2.
Proof.
intros.
generalize H.
clear H.
induction l1.
(* base *)
simpl.
intro H12.
right; assumption.
(* ind *)
intros.
simpl in H.
destruct H as [H1 | H2].
left; simpl.
left; assumption.
destruct IHl1.
assumption.
left; simpl.
right; assumption.
right; assumption.
Qed.

Print rev.

Lemma rev_rev_l : forall (A:Set) (l:list A), rev (rev l) = l.
Proof.
induction l.
(* base *)
simpl; reflexivity.
(* ind *)


(* This auxiliary lemma would help...
Lemma rev_aux : forall (A:Set) (l: list A) (a:A), rev (l ++ (a :: nil)) = a :: (rev l).
*)
Lemma rev_aux : forall (A:Set) (l: list A) (a:A), rev (l ++ (a :: nil)) = a :: (rev l).
Proof.
induction l.
simpl.
reflexivity.
intro. simpl.
rewrite IHl.
simpl; reflexivity.
Qed.

(* ... continuing the proof *)

simpl.
rewrite rev_aux.
simpl.
rewrite IHl.
reflexivity.
Qed.


Print nat.

(* A property (predicate) on natural numbers *)
Inductive Even : nat -> Prop :=
| Even_base : Even 0
| Even_step : forall n, Even n -> Even (S (S n)).

Print plus.


Lemma not_1_even : ~(Even 3).
Proof.
red.
intro.
inversion H.
inversion H1.
Qed.



Proposition sum_even : forall n m:nat, Even n -> Even m -> Even (n+m).
Proof.
intros.
induction H.
(* base *)
simpl; assumption.
(* ind *)
simpl.
apply Even_step.
assumption.
Qed.


Lemma  s_n_even : forall n:nat, Even n -> ~ Even (1+n).
Proof.
intros.
simpl.
elim H.
(* base *)
red.
intro.
inversion H0.
(* ind *)
intros n0 H1 H2.
intro H3.
apply H2.
simpl.
inversion H3.
exact H4.
Qed.

Lemma double_even : forall n:nat, Even (2*n).
Proof.
intros.
simpl.
elim n.
simpl.
constructor.  (* apply Even_base. *)

intros.
simpl.

cut (forall x y:nat, x+(S y) = S (x+y)).

intros.
rewrite H0.
constructor. (* apply Even_step. *)
assumption.

clear H.
intros.
induction x.
  reflexivity.

  simpl.
  rewrite IHx.
  reflexivity.
Qed.

(*
 Exercise: rewrite the prove of the previous lemma without using the cut tactic.
           Hint: use the command "SearchAbout plus." to find out a useful lemma in the database.

 Lemma double_even' : forall n:nat, Even (2*n).
*)






(*
 Exercise: define the "Odd" predicate and prove that for every n, (Even n)->(Odd (S n)).
*)





(* An inductive relation "x is the last element of list l" *)
Inductive Last (A:Type) (x:A) : list A -> Prop :=
| last_base : Last x (cons x nil)
| last_step : forall l y, Last x l -> Last x (cons y l).


Lemma last_nil : forall (A:Type) (x:A), ~(Last x nil).
Proof.
intros.
intro.
inversion H.
Qed.


(* The prove of  ~(Last x nil)  without using the inversion tactic. *)
Lemma last_nil_aux : forall (A:Type) l (x:A), Last x l -> l=nil -> False.
intros A l x H. elim H.
  intro H0. discriminate H0.
  intros. discriminate H2.
Qed.

Theorem last_nil' : forall (A:Type) (x:A), ~(Last x nil).
intros. red. intros.
apply last_nil_aux with A nil x.
assumption.
reflexivity.
Qed.





(* Exercise: 
Lemma rev_last : forall (A:Type) (x:A) (l: list A), (Last x (rev (x::l))).
(* An auxiliary lemma can be useful! *)

*)




(* An example of mutually defined inductive types *)
Inductive EVEN : nat -> Prop :=
| EVEN_base : EVEN 0
| EVEN_step : forall n, ODD n -> EVEN (S n)
with ODD : nat -> Prop :=
| ODD_step : forall n, EVEN n -> ODD (S n).


(* Prove properties of natural numbers with these predicates. *)


