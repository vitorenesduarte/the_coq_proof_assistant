Section ExerciseOne.

Lemma Ex1A : forall a b c : Prop, (a \/ b) \/ c -> a \/ (b \/ c).
Proof.
intros a b c H.
destruct H as [HO | H3].
destruct HO as [H1 | H2].
  left.
  exact H1.
  right.
  left.
  exact H2.
  right.
  right.
  exact H3. 
Qed.

Lemma Ex1B : forall a b c : Prop, (b -> c) -> a \/ b -> a \/ c.
intros a b c H1 H2.
destruct H2 as [H3 | H4].
  left.
  exact H3. 
  right.
  apply H1.
  exact H4. 
Qed.

Lemma Ex1C : forall a b c : Prop, (a /\ b) /\ c -> a /\ (b /\ c). 
intros a b c H. 
destruct H as [HO H3].
destruct HO as [H1 H2].
  split.
    exact H1.
    split.
      exact H2. 
      exact H3. 
Qed.

Lemma Ex1D : forall a b c : Prop, a \/ (b \/ c) -> (a \/ b) \/ (a \/ c).
intros a b c H.
destruct H as [HO | H3].
  left.
  left.
  exact HO.
  destruct H3 as [H1 | H2].
    left.
    right.
    exact H1.
    right.
    right.
    exact H2.
Qed.

Lemma Ex1E : forall a b c : Prop, (a /\ b) \/ (a /\ c) <-> a /\ (b \/ c).
intros a b c.
split.
  (* left to right *)
  intros H.
  split.
    destruct H as [H1 | H2].
    destruct H1 as [H3 H4].
    exact H3.
    destruct H2 as [H5 H6].
    exact H5.
  destruct H as [H1 | H2].
  destruct H1 as [H3 H4].
  left.
  exact H4.
  destruct H2 as [H5 H6].
  right.
  exact H6.
  (* right to left *)
  intros H. 
  destruct H as [H1 H2]. 
  destruct H2 as [H3 | H4].
  left.
  split.
  exact H1.
  exact H3.
  right.
  split.
  exact H1.
  exact H4.
Qed.

Lemma Ex1F : forall a b c : Prop, (a \/ b) /\ (a \/ c) <-> a \/ (b /\ c).
Proof.
intros a b c.
split.
  (* left to right *)
  intros H.
  destruct H as [H1 H2].
  destruct H1 as [H3 | H4].
  left; exact H3.
  destruct H2 as [H5 | H6].
  left; exact H5.
  right.
  split.
    exact H4.
    exact H6.
  (* right to left *)
  intro H.
  split; destruct H as [H1 | H2].
    left; exact H1.
    destruct H2 as [H3 H4].
    right; exact H3.
    left; exact H1.
    destruct H2 as [H3 H4].
    right; exact H4.
Qed.
