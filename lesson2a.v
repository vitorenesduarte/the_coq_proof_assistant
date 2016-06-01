Require Import ZArith.

(* ================================================================== *)
(* ================ Coq as a Programming Language =================== *)

(* prints the definition of an identifier *)
Print nat.

(* check the type of an expression *)
Check S (S O).


(* defining new constants *)

(* using the eliminators *)
Definition double : nat->nat := nat_rec (fun _ => nat) 0 (fun x y => S (S y)).

Check double.
Print double.

(* using general recursion *)
Fixpoint double'  (n : nat) : nat := 
  match n with 
  | O => O 
  | S x => S (S (double' x))
  end.

Definition triple := fun x : nat => x + (double x).

Definition quadruple (x:nat) : nat := (double' x) + (double' x).

Check triple.

(* performs evaluation of an expression
   strategy: call-by-value;  reductions: delta*)
Eval cbv delta [double] in (double 22).

(* "Eval compute" is equivalent to "Eval cbv delta beta iota zeta" *) 
Eval compute in (double 22).

Eval compute in (double' 15).

Eval compute in triple (double 10).

Eval compute in (quadruple 5).


(* ================================================================== *)
(* ================== Interpretation Scopes ========================= *)


(* some notations are overloaded *)

(* to find the function hidden behind a notation *)
Locate "+".
Locate "*".

Print Scope nat_scope.
Print Scope Z_scope.

Locate "*".

Check 3.
Eval compute in 4+5.

Check (3*5)%Z.  (* "term%key" bounds the interpretation of "term" to the scope "key" *)
Eval compute in (3 + 5)%Z.


(* When a given notation has several interpretations, 
   the most recently opened scope takes precedence. *)
Open Scope Z_scope.


Check 3.
Check (S (S (S O))).
Eval compute in 7*3.

Close Scope Z_scope.

Check 3.



(* ================================================================== *)
(* ===================== Implicit Arguments ========================= *)


Definition comp : forall A B C:Set, (A->B) -> (B->C) -> A -> C
  := fun A B C f g x => g (f x).

Definition example0 (A:Set) (f:nat->A) := comp _ _ _ S f.

Print example0.

Set Implicit Arguments.

Definition comp1 : forall A B C:Set, (A->B) -> (B->C) -> A -> C
  := fun A B C f g x => g (f x).

Definition example1 (A:Set) (f:nat->A) := comp1 S f.

Check (comp1 (C:=nat) S).

Check (@comp1 nat nat nat S S).

Unset Implicit Arguments.

Definition comp2 : forall A B C:Set, (A->B) -> (B->C) -> A -> C
  := fun A B C f g x => g (f x).

Implicit Arguments comp2 [A C].

Definition example2 (A:Set) (f:nat->A) := comp2 nat S f.

Print Implicit example2.
Print Implicit comp2.


Set Implicit Arguments.


(* ================================================================== *)
(* ====================== Proof irrelevance ========================= *)

Section ProofIrrelevance.
  
Variable P : Prop.

Theorem t1 : P -> P.
Proof (fun x => x).

Lemma t2 :  P -> P.
Proof.
  exact (fun x => x).
Qed.

Definition t3 (x:P) :P := x.

Let t4 (x:P) :P := x.

Variable a:P.

Eval compute in t1 a.
Eval cbv delta in t1 a.
Eval cbv delta in t3 a.
Eval compute in t3 a.
Eval compute in t2 a.
Eval cbv delta in t2 a.
Eval cbv delta in t4 a.
Eval compute in t4 a.

End ProofIrrelevance.


(* ================================================================== *)
(* ===================== Finding existing proofs ==================== *)

Section Examples.
        
Search le.

SearchPattern (_ + _ <= _ + _).

SearchRewrite (_+(_-_)).

SearchAbout ge.

Lemma ex16 : 1 <= 3.
Proof.
SearchPattern (_ <= _).
apply le_S.
apply le_S.
apply le_n.
Qed.           (* The automatic tactic "firstorder" would solve the goal. *)



Lemma ex17 : forall x y:nat, x <= 5 -> 5 <= y -> x <= y.
Proof.
intros x y.
intro H.
intro H1.
Search le.
apply le_trans with (m := 5).
assumption.
assumption.
Qed.

Lemma ex18 : forall n:nat, n+n = 2*n.
Proof.       (* reflexivity – reflexivity property for equality. *)
intro n.
SearchRewrite (_ * _).
rewrite mult_succ_l with (m := n).
rewrite mult_succ_l with (m := n).
SearchRewrite( 0 * _).
rewrite mult_0_l.
SearchRewrite( 0 + _).
rewrite plus_O_n.
reflexivity.
Qed.

Lemma ex19 : forall x y:nat, (x + y) * (x + y) = x*x + 2*x*y + y*y.
Proof.              
intros x y.
SearchRewrite ((_ + _) * _).
rewrite mult_plus_distr_r.
SearchRewrite (_ * (_ + _)).
rewrite mult_plus_distr_l.
rewrite mult_plus_distr_l.
SearchRewrite (_ + (_ + _)).
rewrite plus_assoc.
rewrite <- plus_assoc with (n := x * x).
SearchPattern (?x * ?y = ?y * ?x).
rewrite mult_comm with (n := y)  (m := x).
SearchRewrite (2 * _).
rewrite ex18.
SearchRewrite (_ * (_ * _)).
rewrite mult_assoc.
reflexivity.
Qed.

Lemma ex20 : forall n:nat, n <= 2*n.
Proof.
intro n.
induction n.
(* base *)
SearchRewrite (_ * 0).
rewrite mult_0_r.
reflexivity.
(* ind step *)
simpl.
Search le.
apply le_n_S.
SearchPattern (_ <= _ + _).
apply le_plus_l.
Qed.

End Examples.