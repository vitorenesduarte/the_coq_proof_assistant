Section InAHurry.

Lemma AndComm : forall a b : Prop, a /\ b -> b /\ a.
Proof.
intros a b H.
split.
  destruct H as [H1 H2].
  exact H2. 
  destruct H as [H1 H2].
  exact H1. 
Qed.

Lemma AndComm2 : forall a b : Prop, a /\ b -> b /\ a.
Proof.
intros a b H.
split; destruct H as [H1 H2].
  exact H2.
  exact H1. 
Qed.

Lemma OrComm : forall a b : Prop, a \/ b -> b \/ a.
Proof.
intros a b H.
destruct H as [H1 | H2].
  right.
  exact H1.
  left.
  exact H2.
Qed.
