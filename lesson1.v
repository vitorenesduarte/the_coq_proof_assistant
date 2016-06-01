(* ================================================================== *)
Section EX.

Variables (A:Set) (P : A->Prop).
Variable Q:Prop.

(* Check the type of an expression. *)
Check P.  

Lemma trivial : forall x:A, P x -> P x.
Proof.
intros x H.
exact H.
Qed.


(* Prints the definition of an identifier. *)
Print trivial.


Lemma example : forall x:A, (Q -> Q -> P x) -> Q -> P x.
Proof.
intros x H1 H2.
apply H1.
exact H2.
exact H2.
Qed.

Print example.

End EX.

Print trivial.
Print example.
(* ================================================================== *)




(* ================================================================== *)
(* ====================== Propositional Logic ======================= *)
(* ================================================================== *)

Section ExamplesPL.

Variables Q P :Prop.

Lemma ex1 : (P -> Q) -> ~Q -> ~P.
Proof.
intros H1 H2.
intro H3.
apply H2.
apply H1.
exact H3.
Qed.

Print ex1.

Lemma ex1' : (P -> Q) -> ~Q -> ~P.
Proof.
intros H1 H2.
intro H3.
apply H2.
apply H1.
exact H3.
Qed.

Print ex1'.


Lemma ex2 : P /\ Q -> Q /\ P.
Proof.
intro H1.
destruct H1 as [H2 H3].
split.
exact H3.
exact H2.
Qed.


Lemma ex3 : P \/ Q -> Q \/ P.
Proof.
intro H.
destruct H as [H1 | H2].
right; assumption.
left; assumption.
Qed.



Theorem ex4 : forall A:Prop, A -> ~~A.
Proof.
intro A.
intro H1.
intro H2.
apply H2.
exact H1.
Qed.

Lemma ex4' : forall A:Prop, A -> ~~A.
Proof.
intros A H1.
red.
intro H2.
unfold not in H2.
apply H2.
exact H1.
Save.




Axiom double_neg_law : forall A:Prop, ~~A -> A.  (* classical *)

(* CAUTION: Axiom is a global declaration. 
   Even after the section is closed double_neg_law is assume in the enviroment, and can be used. 
   If we want to avoid this we should decalre double_neg_law using the command Hypothesis. 
*)  


Lemma ex5 : (~Q -> ~P) -> P -> Q.   (* this result is only valid classically *)
Proof.
intros H1 H2.
apply double_neg_law.
intro H3.
apply H1.
exact H3.
exact H2.
Qed.


Lemma ex6 : (P\/Q)/\~P -> Q.   
Proof.
intro H1.
destruct H1 as [H2 H3].
apply double_neg_law.
intro H4.
destruct H2 as [H5 | H6].
apply H3.
exact H5.
apply H4.
exact H6.
Qed.


Lemma ex6' : (P\/Q)/\~P -> Q.   
Proof.
intros H1.
destruct H1 as [H2 H3].
destruct H2 as [H4 | H5].
contradiction.
exact H5.
Qed.

Lemma ex7 : ~(P \/ Q) <-> ~P /\ ~Q.   
Proof.
split.
  (* left to right *)
  intro H.
  split.
    unfold not in H.
    intro H1.
    apply H.
    left; assumption.
    intro H2.
    apply H.
    right; assumption.
  (* right to left *)
  intro H.
  intro H1.
  destruct H as [H2 H3].
  destruct H1 as [H4 | H5].
  apply H2.
  exact H4.
  apply H3.
  exact H5.
Qed.


Lemma ex7' : ~(P \/ Q) <-> ~P /\ ~Q.
Proof.
tauto.
Qed.



Variable B :Prop.
Variable C :Prop.


(* exercise *)
Lemma ex8 : (P->Q) /\ (B->C) /\ P /\ B -> Q/\C. 
Proof.
intro H.
destruct H as [H1 H2].
destruct H2 as [H3 H4].
destruct H4 as [H5 H6].
split.
  apply H1.
  exact H5.
  apply H3.
  exact H6.
Qed.
 
(* exercise *)
Lemma ex9 : ~ (P /\ ~P).   
Proof.
intro H.
destruct H as [H1 H2].
apply H2.
exact H1.
Qed.

End ExamplesPL.

(* ================================================================== *)
(* =======================  First-Order Logic ======================= *)
(* ================================================================== *)

Section ExamplesFOL.

Variable X :Set.
Variable t :X. 
Variables R W : X -> Prop.

Lemma ex10 : R(t) -> (forall x, R(x)->~W(x)) -> ~W(t).
Proof.
intros H1.
intros H2.
apply H2.
exact H1.
Qed.


Lemma ex11 : forall x, R x -> exists x, R x.
Proof.
intro x.
intro H1.
exists x.
exact H1.
Qed.


Lemma ex11' : forall x, R x -> exists x, R x.
Proof.
firstorder.
Qed.


Lemma ex12 : (exists x, ~(R x)) -> ~ (forall x, R x).
Proof.
intro H.
intro H1.
destruct H as [x H2].
apply H2.
apply H1.
Qed.

(* Exercise *)
Lemma ex13 : (forall x, R x) \/ (forall x, W x) -> forall x, (R x) \/ (W x).
Proof.
intro H.
intro x.
destruct H as [H1 | H2].
left.
apply H1.
right.
apply H2.
Qed.

Variable G : X->X->Prop.

(* Exercise *)
Lemma ex14 : (exists x, exists y, (G x y)) -> exists y, exists x, (G x y).
Proof.
intro H.
destruct H as [x H1].
destruct H1 as [y H2].
exists y.
exists x.
exact H2.
Qed.

(* Exercise *)
Proposition ex15: (forall x, W x)/\(forall x, R x) -> (forall x, W x /\ R x).
Proof.
intro H.
intro x.
destruct H as [H1 H2].
split.
apply H1.
apply H2.
Qed.


(* ------- Note that we can have nested sections ----------- *)
Section Relations.       

Variable D : Set.
Variable Rel : D->D->Prop.

Hypothesis R_symmetric : forall x y:D, Rel x y -> Rel y x.
Hypothesis R_transitive : forall x y z:D, Rel x y -> Rel y z -> Rel x z.


Lemma refl_if : forall x:D, (exists y, Rel x y) -> Rel x x.
Proof.
intro H.
intro H1.
destruct H1 as [y H2].
apply R_transitive with y.
exact H2.
apply R_symmetric.
exact H2.
Qed.

Check refl_if.

End Relations.

Check refl_if. (* Note the difference after the end of the section Relations. *)



(* ====== OTHER USES OF AXIOMS ====== *)

(* --- A stack abstract data type --- *)
Section Stack.

Variable U:Type.

Parameter stack : Type -> Type.
Parameter emptyS : stack U. 
Parameter push : U -> stack U -> stack U.
Parameter pop : stack U -> stack U.
Parameter top : stack U -> U.
Parameter isEmpty : stack U -> Prop.

Axiom emptyS_isEmpty : isEmpty emptyS.
Axiom push_notEmpty : forall x s, ~isEmpty (push x s).
Axiom pop_push : forall x s, pop (push x s) = s.
Axiom top_push : forall x s, top (push x s) = x.

End Stack.

Check pop_push.

(* Now we can make use of stacks in our formalisation!!! *)

(* A NOTE OF CAUTION!!! *)
(* The capability to extend the underlying theory with arbitary axiom 
   is a powerful but dangerous mechanism. We must avoid inconsistency. 
*)
Section Caution.

Check False_ind.

Hypothesis ABSURD : False.

Theorem oops : forall (P:Prop), P /\ ~P.
elim ABSURD.
Qed.

End Caution. (* We have declared ABSURD as an hypothesis to avoid its use outside this section. *)



