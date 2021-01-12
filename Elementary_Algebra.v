Require Export Classification_Axiom_Scheme.
From mathcomp Require Export ssreflect.

Module Algebra.

Definition Union x y := {| λ z, z ∈ x \/ z ∈ y|}.
Notation "x ∪ y" := (Union x y) (at level 65, right associativity).
Hint Unfold Union : set.

Definition Intersection x y := {| λ z, z ∈ x /\  z ∈ y|}.
Notation "x ∩ y" := (Intersection x y)(at level 60, right associativity).

Theorem bel_union x y z :
  z ∈ x \/ z ∈ y <-> z ∈ (x ∪ y).
Proof.
  rewrite Axiom_Scheme; split => [[zx|zy]|[z_ [zx|zy]] ]; Ens.
Qed.

Theorem bel_inter x y z :
  z ∈ x /\ z ∈ y <-> z ∈ (x ∩ y).
Proof.  
  rewrite Axiom_Scheme; split => [[zx zy]| [z_ [zx zy]]]; Ens.
Qed.    

Hint Resolve bel_union bel_inter : set.

Theorem union_fix x :
  x ∪ x = x.
Proof.
  rewrite Axiom_Extent => z; rewrite -bel_union; split => [[H|H]|H]; auto.
Qed.

Theorem inter_fix x :
  x ∩ x = x.
Proof.
  rewrite Axiom_Extent => z.
  rewrite -bel_inter.
  split => [[H _] | H]; auto.
Qed.

Hint Rewrite union_fix inter_fix : set.


Theorem union_com x y :
    x ∪ y = y ∪ x.
Proof.
  extent.
  rewrite -!bel_union.
  split => [[zx | zy]|[zy |zx]]; auto.
Qed.

Theorem inter_com x y :
    x ∩ y = y ∩ x.
Proof.
  extent.
  rewrite -!bel_inter.
  split => [[zx zy]| [zy zx]] //.  
Qed.

Hint Rewrite union_com inter_com : set.

Theorem union_ass x y z :
  (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  extent.
  rewrite -!bel_union.
  split => [[[x_|y_]|z_]|[x_|[y_|z_]]]; auto.
Qed.

Theorem inter_ass x y z :
  (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  extent.
  rewrite -!bel_inter.
  split => [ [ [x_ y_] z_] |[x_ [y_ z_]]]; auto.
Qed.

Theorem union_dist x y z :
  x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  extent; rewrite -!bel_union -!bel_inter -!bel_union.
  split => [[x_ [y_ | z_]]|[[x_ y_]|[x_ z_]]]; auto.
Qed.

Theorem inter_dist x y z :
  x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  extent; rewrite -!bel_union -!bel_inter -!bel_union.
  split => [[x_ | [y_ z_]]|[[x_ | y_] [x__ | z_]]]; auto.
Qed.


Hint Rewrite union_dist inter_dist.

Definition Complement x := {|λ y, ~ y ∈ x|}.
Notation "¬ x" := (Complement x) (at level 5, right associativity).
Hint Unfold Complement : set.

Theorem comp_fix x :
  ¬ ¬ x = x.
Proof.
  extent.
  rewrite !Axiom_Scheme.
  split => [[z_ H]|H].
  + case: (not_and_or _ _ H) => {H} [H | H] => //.
    by apply NNPP.
  + split; Ens.
    apply or_not_and.
    by right.
Qed.

Hint Rewrite comp_fix : set.

Theorem demorgan_union x y :
  ¬ (x ∪ y) = ¬ x ∩ ¬ y.
Proof.
  extent; rewrite Axiom_Scheme -bel_union -bel_inter !Axiom_Scheme.
  split => [ [z_ H] | [[z_ _zx] [_ _zy]] ].
  + by move /not_or_and : H => [_zx _zy].
  + by split => //; apply and_not_or.
Qed.

Theorem demorgan_inter x y :
  ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  extent; rewrite Axiom_Scheme -bel_union -bel_inter !Axiom_Scheme.
  split => [ [z_ H] |  H ].
  + by case /not_and_or : H => [_zx | _zy]; constructor.
  + by case H => [[z_ zx]|[z_ zy]]; apply (conj z_); apply or_not_and; constructor.
Qed.    

Hint Rewrite demorgan_union demorgan_inter : set.

Definition Difference x y := x ∩ (¬ y).
Notation "x ~ y" := (Difference x y) (at level 50, left associativity).
Hint Unfold Difference : set.

Theorem inter_diff x y z :
    x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  by rewrite /Difference inter_ass.
Qed.

Corollary Property_Ineq (x y : Class):
  x <> y <-> y <> x.
Proof.
  split => [F H|F H]; auto.
Qed.

Hint Resolve Property_Ineq : set.

Definition Φ := {|λ x, x <> x|}.
Hint Unfold Φ : set.

Theorem not_bel_zero x :
  ~ x ∈ Φ.
Proof.
  move /Axiom_Scheme => [_ F]; auto.
Qed.

Hint Resolve not_bel_zero : set.

Ltac zero H := case (not_bel_zero _ H).

Theorem zero_union x :
 Φ ∪ x = x.
Proof.
  extent; rewrite -bel_union.
  by split => [[F | zx]|zx] => //; [zero F| right].
Qed.

Theorem zero_inter x:
  Φ ∩ x = Φ.
Proof.
  extent; rewrite -bel_inter.
  split => [[F _]|F]; zero F.
Qed.

Definition μ := {|λ x, x = x|}.

Corollary Property_μ x :
  x ∪ (¬ x) = μ.
Proof.
  extent; rewrite -bel_union !Axiom_Scheme.
  split => [[zx | [z_ _zx]]| [z_ _]]; [split | split |] => //; [Ens|].
  case (classic (z ∈ x)) => [zx | _zx]; [left|right] => //.
Qed.

Hint Unfold μ : set.
Hint Resolve Property_μ : set.

Theorem bel_universe_set x :
  x ∈ μ <-> Ensemble x.
Proof.
  rewrite Axiom_Scheme; split => [[H _]| H] //.
Qed.

Theorem universe_union x :
  x ∪ μ = μ.
Proof.
  extent; rewrite -bel_union bel_universe_set.
  split => [[zx|H]|H] => //; [|right]; Ens.
Qed.

Theorem universe_inter x :
  x ∩ μ = x.
Proof.
  extent; rewrite -bel_inter bel_universe_set.
  split => [[zx z_] | zx] => //.
  split => //; Ens.
Qed.  

Hint Rewrite universe_union universe_inter : set.

Theorem zero_comp_universe :
  ¬ Φ = μ.
Proof.
  extent; rewrite !Axiom_Scheme.
  split => [[z_ H]|[z_ _]]; split => //.
  move => [_ F]; auto.
Qed.



Theorem universe_comp_zero :
  ¬ μ = Φ.
Proof.
  extent; rewrite !Axiom_Scheme.
  split => [[z_ F]|[z_ F]]; split => //.
  move => _; apply F; split => //.
Qed.

Hint Resolve zero_comp_universe universe_comp_zero : set.


Definition Element_I x := {|λ z, forall y, y ∈ x -> z ∈ y|}.
Notation "⊓ x" := (Element_I x)(at level 66).

Definition Element_U x := {|λ z, exists y, z ∈ y /\ y ∈ x|}.
Notation "⊔ x" := (Element_U x)(at level 66).

Hint Unfold Element_I Element_U : set.


Theorem zero_eleI_universe :
  ⊓ Φ = μ.
Proof.
  extent; rewrite !Axiom_Scheme.
  split => [[z_ _] | [z_ _]]; split => // y F; zero F.
Qed.

Theorem zero_eleU_zero :
  ⊔ Φ = Φ.
Proof.
  extent; rewrite !Axiom_Scheme.
  split => [[z_ [y [zy F]]] |[z_ F]]; split => //; zero F.
Qed.

Definition Subclass x y := forall z, z ∈ x -> z ∈ y.
Notation "x ⊂ y" := (Subclass x y) (at level 70).
Hint Unfold Subclass : set.

Theorem zero_sub x :
  Φ ⊂ x.
Proof.
  move => z F; zero F.
Qed.

Theorem sub_universe x :
  x ⊂ μ.
Proof.
  move => z zx; rewrite bel_universe_set; Ens.
Qed.

Hint Resolve zero_sub sub_universe : set.

Theorem sub_eq x y :
  (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  split => [[xy yx] | H].
  + extent; split => [zx | zy].
    - apply (xy z zx).
    - apply (yx z zy).
  + subst y.
    by suff xx :  (x ⊂ x).
Qed.

Hint Resolve sub_eq : set.

Theorem sub_tran x y z :
  x ⊂ y -> y ⊂ z -> x ⊂ z.
Proof.
  move => xy yz p px; auto.
Qed.

Theorem union_sub x y :
  x ∪ y = y <-> x ⊂ y.
Proof.
  split => [H p px|xy].
  + by rewrite -H -bel_union; left.
  + extent; rewrite -bel_union.
    split => [[zx | zy]|zy] => //.
    - apply (xy z zx).
    - by right.
Qed.

Hint Resolve union_sub : set.

Theorem sub_ele x y :
  x ⊂ y -> (⊔  x ⊂ ⊔ y) /\ (⊓ y ⊂ ⊓ x).
Proof.
  move => xy; split => [p|p]; rewrite !Axiom_Scheme; case => p_ H; split => //.
  + case H => [q [pq qx]].
    exists q; split => //.
    apply (xy q qx).
  + move => q qx.
    apply H.
    by apply xy.
Qed.

Theorem bel_ele x y :
  x ∈ y -> (x ⊂ ⊔ y) /\ (⊓ y ⊂ x).
Proof.
  move => xy; split => z; rewrite Axiom_Scheme => H.
  + Ens.
  + case H => {H} [z_ H].
    by apply H.
Qed.

Hint Resolve bel_ele : set.

Definition ProperSubclass x y := x ⊂ y /\ x <> y.
Notation "x ⊆ y" := (ProperSubclass x y)(at level 70).

Corollary Property_ProperSubclass x y :
  x ⊂ y -> (x ⊆ y ) \/ x = y.
Proof.
  case (classic (x = y)) => [xy | xy]; [right|left] => //.
Qed.


Hint Unfold ProperSubclass : set.
Hint Resolve Property_ProperSubclass : set.

Lemma bel_diff x y z :
  z ∈ x /\ ~ z ∈ y <-> z ∈ (x ~ y).
Proof.
  rewrite !Axiom_Scheme.
  split => [[zx _zy]|[z_ [zx [_ _zy]]]] => //.
  suff H : Ensemble z; by Ens.
Qed.     

Lemma diff_zero x :
  x ~ x = Φ.
Proof.
  extent; rewrite -bel_diff.
  split => [[T F]|F] //; zero F.
Qed.    

Lemma Property_Φ x y :
  y ⊂ x -> x ~ y = Φ <-> x = y.
Proof.
  move => yx.
  split => [H | H]; extent.
  + move: (not_bel_zero z); rewrite -H -bel_diff.
    move /not_and_or; case => H0; split => [zx|zy] //.
    - by apply yx.
    - by apply NNPP.
    - by apply yx.
  + subst y.
    by rewrite diff_zero.
Qed.

Hint Resolve Property_Φ : set.

End Algebra.

Export Algebra.


    


   




























  
















