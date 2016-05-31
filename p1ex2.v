Section ExerciseTwo.

Variable X : Set.
Variable P Q R : X -> Prop.

Lemma Ex2A : (exists x, (P x) /\ (Q x)) -> (exists x, (P x)) /\ (exists x, (Q x)).
intros H.
split.
  destruct H as [x H1].
  destruct H1 as [H2 H3].
  exists x.
  exact H2.
  destruct H as [x H1].
  destruct H1 as [H2 H3].
  exists x.
  exact H3.
Qed.

Variable A : X -> X -> Prop.

Lemma Ex2B : (exists x, forall y, (A x y)) -> (forall y, exists x, (A x y)).
intros H.
destruct H as [x H2].
intro H3.
exists x.
apply H2.
Qed.

Lemma Ex2C : (exists x, (P x)) -> (forall x y, (P x) -> (Q y)) -> (forall y, (Q y)).
intros H1 H2.
intros H3.
elim H1.
intros H4.
apply H2.
Qed.

Lemma Ex2D : (forall x, (Q x) -> (R x)) -> (exists x, (P x) /\ (Q x)) -> (exists x, (P x) /\ (R x)).
intros H1 H2.
destruct H2 as [x H3].
exists x.
destruct H3 as [H4 H5].
split.
  exact H4.
  apply H1.
  exact H5.
Qed.

Lemma Ex2E : (forall x, (P x) -> (Q x)) -> (exists x, (P x)) -> (exists y, (Q y)).
Proof.
intros H1 H2.
destruct H2 as [x H3].
exists x.
apply H1.
exact H3.
Qed.

Lemma Ex2F : (exists x, (P x)) \/ (exists x, (Q x)) <-> (exists x, (P x) \/ (Q x)).
Proof.
split.
  (* left to right *)
  intros H1.
  destruct H1 as [H2 | H3].
  destruct H2 as [x H4].
  exists x.
  left; exact H4.
  destruct H3 as [x H5].
  exists x.
  right; exact H5.
  (* right to left *)
  intros H1.
  destruct H1 as [x H2].
  destruct H2 as [H3 | H4].
  left.
  exists x.
  exact H3.
  right.
  exists x.
  exact H4.
Qed.
