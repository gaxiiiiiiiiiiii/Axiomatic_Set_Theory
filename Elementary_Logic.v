
Require Export Classical.
From mathcomp Require Import ssreflect.

Module Logic.

Proposition Lemma_x : forall x : Prop, x -> x /\ x.
Proof.
  move => X x; split; auto.
Qed.

Ltac double H := apply Lemma_x in H; destruct H.

Proposition Lemma_xy : forall (x y : Prop), x -> y -> x /\ y.
Proof.
  move => X Y x y; split; auto.
Qed.

Ltac add y  H := apply (Lemma_xy _ y) in H; auto.

Proposition definition_not : forall A B,  (A <-> B) -> (~ A) -> (~ B).
Proof.
  by move => A B H _a b; apply _a; apply H.
Qed.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity, format "'[ ' 'λ' x .. y ']' , t").

Hint Resolve Lemma_x Lemma_xy : set.  

End Logic.

Export Logic.