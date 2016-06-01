Require Import List.


Lemma Ex2A : forall (A:Type) (l:list A), length (rev l) = length l.
Proof.
induction l.
(* base *)
simpl.
reflexivity.
(* ind *)
simpl.
SearchAbout length.
rewrite app_length.
simpl.
rewrite IHl.
SearchAbout plus.
apply Plus.plus_comm.
Qed.

Lemma Ex2B : forall (A B:Type) (f:A->B) (l:list A), length (map f l) = length l.
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


Lemma Ex2C : forall (A B:Type) (f:A->B) (l:list A), rev (map f l) = map f (rev l).
Proof.
induction l.
(* base *)
simpl.
reflexivity.
(* ind *)
simpl.
rewrite IHl.
SearchAbout map.
rewrite map_app.
SearchAbout map.
reflexivity.
Qed.
