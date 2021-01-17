Require Export Elementary_Algebra.

Module Existence.

Axiom Axiom_Subsets : forall (x : Class),
  Ensemble x -> exists y, Ensemble y /\ (forall z, z ⊂ x -> z ∈ y).
    
Hint Resolve Axiom_Subsets : set.

Theorem sub_set x z :
  Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  move => x_ zx.
  case (Axiom_Subsets x x_) => [y [y_ H]].
  move : (H z zx) => {H} zy.
  Ens.
Qed.

Theorem universe_eleU :
  μ = ⊔ μ.
Proof.
  extent; rewrite !Axiom_Scheme.
  split => [[z_ _]|[z_ [y [zy y_]]]]; split => //.
  move : (Axiom_Subsets z z_) => [y [y_ Hy]].
  exists y; split.
  + by apply Hy.
  + by apply bel_universe_set.
Qed.

Theorem universe_eleI :
  Φ = ⊓ μ.
Proof.
  extent; rewrite !Axiom_Scheme.
  split => [[z_ F]|[z_ H]]; split => // _.
  apply (not_bel_zero z).
  apply (H Φ).
  apply bel_universe_set.
  apply sub_set with (x:=z) => //.
  move => x F.
  zero F.
Qed.

Hint Rewrite universe_eleI universe_eleU : set.

Lemma not_zero_exist_bel x :
  x <> Φ -> exists z, z ∈ x.
Proof.
  move => H.
  apply NNPP => F.
  apply H.
  move /not_ex_all_not : F => F.
  extent; split => [zx|zz].
  + case ((F z) zx).
  + zero zz.
Qed.    


Theorem not_zero_set_eleI x : 
  x <> Φ -> Ensemble (⊓ x).
Proof.
  move /not_zero_exist_bel => [z zx].
  case (bel_ele z x zx) => [L R].
  apply sub_set with (x := z); Ens.
Qed.

Hint Resolve not_zero_exist_bel not_zero_set_eleI : set.

Definition PowerClass x := {|λ y, y ⊂ x|}.
Notation "pow( x )" := (PowerClass x) (at level 0, right associativity).
Hint Unfold PowerClass : set.

Theorem bel_pow x y :
  Ensemble y -> x ⊂ y <-> x ∈ pow(y).
Proof.
  rewrite Axiom_Scheme => x_; split => [H |[L R]] => //.
  split => //; apply sub_set with (x:=y) => //.
Qed.

Theorem universe_pow : 
  μ = pow(μ).
Proof.
  extent; rewrite !Axiom_Scheme.
  split => [[z_ _]|[z_ zu]]; split => //.
  move => x xz; rewrite bel_universe_set; Ens.
Qed.

Hint Rewrite universe_pow.

Lemma eleU_pow x :
  Ensemble x -> ⊔ pow(x) = x.
Proof.
  move => x_ ; extent; rewrite !Axiom_Scheme.
  split => [[z_ [y [zy yp]]]|zx].
  + apply Axiom_Scheme in yp.
    case yp => [y_ yx].
    by apply yx.
  + split; first by Ens.
    exists x; split => //.
    rewrite Axiom_Scheme; split => //.
Qed.

Lemma pow_zero :
  forall x, x ∈ pow(Φ) -> x = Φ.
Proof.
  move => x; rewrite Axiom_Scheme; case => [x_ xz].
  extent;split => [zx | F].
  + by apply xz.
  + zero F.
Qed.    



Theorem pow_set x y :
  Ensemble x -> Ensemble pow(x) /\ (y ⊂ x <-> y ∈ pow(x)).
Proof.
  move => x_.
  move :(Axiom_Subsets x x_) => [z [z_ Hz]].
  split.
  + apply sub_set with (x:=z) => //.
    move => p; rewrite Axiom_Scheme; case => [p_ px].
    by apply Hz.
  + split => [yz | yP].
    - rewrite Axiom_Scheme; split => //.
      by apply sub_set with (x := x).
    - by move /Axiom_Scheme : yP => [y_ yx].
Qed.

Hint Resolve pow_set : set.

Definition R := {|λ x, ~ x ∈ x|}.

Lemma Russell_N :
  ~ Ensemble R.
Proof.
  case (classic ({|λ x, ~ x ∈ x|} ∈ {|λ x, ~ x ∈ x|})); rewrite Axiom_Scheme.
  + case => U_ HU F.
    apply HU.
    rewrite Axiom_Scheme; split => //.
  + move => H F; apply H.
    case /not_and_or : H => H //.
    split => //.
    move /NNPP : H => H.
    by move  /Axiom_Scheme : H => [_ H].
Qed.



Theorem universe_notset :
  ~ Ensemble μ.
Proof.
  move => F.
  apply Russell_N.
  apply sub_set with (x := μ) => //.
  apply sub_universe.
Qed.

Hint Resolve Russell_N universe_notset : set.


Definition Singleton x := {|λ z, Ensemble z -> z = x|}.
Notation "[ x ]" := (Singleton x) (at level 0, right associativity).
Hint Unfold Singleton : set.

Theorem set_bel_sing_eq x :
  Ensemble x -> (forall y, y ∈ [x] <-> y = x).
Proof.
  move => x_; split => [H | yx].
  + move /Axiom_Scheme : H => [y_ H]; auto.
  + by subst y; rewrite Axiom_Scheme.
Qed.

Hint Resolve set_bel_sing_eq : set.

Theorem sing_set x :
  Ensemble x -> Ensemble [x].
Proof.      
  move => x_.
  move : (Axiom_Subsets x x_) => [y [y_ Hy]].
  apply sub_set with (x:= pow(x)).
  + by apply pow_set.
  + move => p px.
    apply Axiom_Scheme; split; Ens.
    move /Axiom_Scheme : px => [p_ Hp].
    by rewrite (Hp p_).
Qed.

Hint Resolve sing_set : set.

Lemma bel_sing x y :
 Ensemble x -> x ∈ [y] <-> x = y.
Proof.
  move => x_; rewrite Axiom_Scheme.
  split => [[_ H]|H];auto.
Qed.

Theorem sing_eq_universe_iff_not_set x : 
  [x] = μ <-> ~ Ensemble x.
Proof.
  split => [H x_| _x].
  + apply universe_notset.
    rewrite -H.
    by apply sing_set.
  + extent; rewrite bel_universe_set; split => [xz|z_].
    - Ens.
    - rewrite Axiom_Scheme; split => // _.
      move : (Axiom_Subsets z z_) => [y [y_ Hy]].
      rewrite Axiom_Extent => p.      
      split => [pz|px].
Abort.

Theorem sing_eq_universe_iff_not_set x : 
  [x] = μ -> ~ Ensemble x.
Proof.
  move => H F.
  apply universe_notset.
  rewrite -H.
  by apply sing_set.
Qed.  


Lemma sub_sing x y:
  Ensemble x -> x ⊂ [y] <-> x = [y] \/ x = Φ.
Proof.
  move => x_; split => [H|H].
  + case (classic (x = Φ)) => [Hz|Hz];[by right|left].
    extent; split => [zx|zy].
    - by apply H.
    - move /Axiom_Scheme : zy => [z_ zy].
      rewrite (zy z_) => {z_ zy}.
      move : (not_zero_exist_bel x Hz) => [p px].
      move : (H p px) => py.
      move /Axiom_Scheme : py => [p_ py].
      by rewrite <- (py p_).
  + case H => {H}[H|H]; subst x => //.
    apply zero_sub.
Qed.    

Lemma sing_pow x y:
  Ensemble [x] -> Ensemble y-> y ∈ pow([x]) <-> y = [x] \/ y = Φ.    
Proof.
  move => x_ y_.
  rewrite -bel_pow => //; split => [yx |H]; apply sub_sing => //.
Qed.  





Theorem sing_set_inv x :
  Ensemble [x] -> Ensemble x.
Proof.
  move => x_.
  apply NNPP => F.
  move : x_.
Abort.





Theorem sing_eleI x : 
  Ensemble x -> ⊓[x] = x.
Proof.
  move => x_;  extent; rewrite !Axiom_Scheme.
  split => [[z_ H]|H].
  + apply H.
    by apply bel_sing.
  + split; first by Ens.
    move => y; rewrite Axiom_Scheme; case => [y_ Hy].
    by rewrite (Hy y_).
Qed.

Theorem sing_eleU x :
    Ensemble x -> ⊔ [x] = x.
Proof.
  move => x_; extent; rewrite Axiom_Scheme.
  split => [[z_ [y [zy yx]]]|H].
  + move /Axiom_Scheme : yx => [y_ Hy].
    by rewrite -(Hy y_).
  + split;Ens.
    exists x; split => //; rewrite Axiom_Scheme; split => //.
Qed.

Hint Resolve sing_eleI sing_eleU : set.



Theorem not_sing_eleI x :
    ~ Ensemble x -> ⊓ [x] = Φ /\ ⊔ [x] = x.
Proof.
Abort.

Axiom union_set : forall x y,
  Ensemble x -> Ensemble y -> Ensemble (x ∪ y).


    
Theorem Axiom_Union' x y :
  Ensemble (x ∪ y) -> Ensemble x /\ Ensemble y.
Proof.
  move => H.
  split; apply sub_set with (x := x ∪ y) => // p Hp; rewrite -bel_union; [left|right] => //.
Qed.

Hint Resolve union_set Axiom_Union': set.

Definition Unordered x y := [x] ∪ [y].
Notation "<| x , y |>" := (Unordered x y)(at level 0).
Hint Unfold Unordered : set.

Theorem Unordered_set x y :
  Ensemble x -> Ensemble y -> Ensemble <|x,y|>.
Proof.    
  move => x_ y_.
  apply union_set; apply sing_set => //.
Qed.

Theorem bel_unordered x y z:
  Ensemble x -> Ensemble y -> z ∈ <|x,y|> <-> (z = x \/ z = y).
Proof.
  move => x_ y_; split; rewrite -bel_union => H.
  + case : H => [H|H]; have z_ : Ensemble z by Ens.
    by apply (bel_sing z _ z_) in H; subst z; left.
    by apply (bel_sing z _ z_) in H; subst z; right.
  + case H => {H} [H|H]; subst z; [left|right]; apply bel_sing => //.
Qed.

Hint Resolve Unordered_set bel_unordered : set.

Theorem unord_notset : forall x y, <|x,y|> = μ <-> ~ Ensemble x \/ ~ Ensemble y.
Abort.


Theorem unord_eleI x y :
  Ensemble x -> Ensemble y -> ⊓ <|x,y|> = x ∩ y.
Proof.
  move => x_ y_; extent; split; rewrite !Axiom_Scheme => [[z_ H]]; split => //.
  + split; apply H; apply bel_unordered => //; [left|right] => //.
  + case : H => [zx zy] p. case /(bel_unordered x y p x_ y_); move -> => //.
Qed.

Theorem unord_eleU x y :
  Ensemble x -> Ensemble y -> ⊔ <|x,y|> = x ∪ y.
Proof.
  move => x_ y_;  extent; split; rewrite !Axiom_Scheme => [[z_ H]]; split => //.
  + case : H => [p [zp H]]; case /(bel_unordered x y p x_ y_) : H; move <-; [left|right] => //.
  + case H => [zx|zy]; [exists x|exists y]; split => //; apply bel_unordered => //; [left|right] => //.
Qed.

Hint Resolve unord_eleU unord_eleI : set.


Theorem unord_ele_not : forall x y,
  ~ Ensemble x \/ ~ Ensemble y -> (⊓<|x,y|> = Φ) /\ (⊔ <|x,y|> = μ).
Abort.

End Existence.

Export Existence.






    

    
  













  



  

    


    


