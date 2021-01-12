Require Export Elementary_Logic.
Require Export Coq.Setoids.Setoid.

Module Classification.

Parameter Class : Type.

Parameter In : Class -> Class -> Prop.
Notation "x ∈ y" := (In x y) (at level 10).

Axiom Axiom_Extent : forall x y,
  x = y <-> (forall z, z ∈ x <-> z ∈ y).

Ltac extent := rewrite Axiom_Extent; intro.

Hint Resolve Axiom_Extent : set.

Definition Ensemble (x : Class) : Prop := exists y, x ∈ y.

Ltac Ens := unfold Ensemble; eauto.
Ltac AssE x := assert (Ensemble x); Ens.

Hint Unfold Ensemble : set.

Parameter Classifier : (Class -> Prop) -> Class.
Notation "{| P |}" := (Classifier P)(at level 0).

Axiom Axiom_Scheme : forall (b : Class) (P : Class -> Prop),
  b ∈ {| P |} <-> Ensemble b /\ (P b).

Hint Resolve Axiom_Scheme : set.


End Classification.

Export Classification.




