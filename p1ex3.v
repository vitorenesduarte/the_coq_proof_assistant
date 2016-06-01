Section ExerciseThree.

Axiom ExcludedMidlle : forall A : Prop, A \/ ~A.

Lemma Ex3A : forall a b : Prop, ((a -> b) -> a) -> a.
Proof.
intros a b H.
Admitted.


Lemma Ex3B : forall a : Prop, ~~a -> a.
Proof.
intros a.
intro H.
destruct H.
(* how can I apply excluded middle now? *)
Admitted.

Variable X : Set.
Variable P : X -> Prop.

Lemma Ex3C : forall x, (P x) -> exists x, ~(P x).
Proof.
intros a H.
exists a.
(* how can I apply excluded middle now? *)
Admitted.
