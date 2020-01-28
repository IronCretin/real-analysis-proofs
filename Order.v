Require Import Ensembles.


Class TotalOrder (S : Set) (LT : S -> S -> Prop) :=
{ antisym : forall a b, LT a b -> LT b a -> a = b
; trans : forall a b c, LT a b -> LT b c -> LT a c
; connex : forall a b, LT a b /\ LT b a
}.

Definition IsUpperBound {A} {LT} {_ : TotalOrder A LT} (E : Ensemble A) (b: A)
  := forall a, In _ E a -> LT a b.

Definition IsLeastUpperBound {A} {LT} {_ : TotalOrder A LT} (E : Ensemble A) (b: A)
  := IsUpperBound E b /\ (forall c, b = c /\ IsUpperBound E c -> LT b c).
