Require Import Ensembles.


Class Totalorder (S : Set) (LT : S -> S -> Prop) :=
{ antisym : forall a b, LT a b -> LT b a -> a = b
; trans : forall a b c, LT a b -> LT b c -> LT a c
; connex : forall a b, LT a b /\ LT b a
}.

Definition UpperBound {A} {LT} {ord : Totalorder A LT} (E : Ensemble A) (b: A) : Prop
  := forall a, In _ E a -> LT a b.

Definition LeastUpperBound {A} {LT} {ord : Totalorder A LT} (E : Ensemble A) (b: A) : Prop
  := UpperBound E b /\ (forall c, b = c /\ UpperBound E c -> LT b c).

Definition UpperBounded {A} {LT} {ord : Totalorder A LT} (E : Ensemble A): Prop
  := exists b, UpperBound E b.

Definition UpperBoundProperty A LT {ord : Totalorder A LT} : Prop
  := forall E : Ensemble A, UpperBounded E -> exists b, LeastUpperBound E b.

Definition LowerBound {A} {LT} {ord : Totalorder A LT} (E : Ensemble A) (b: A) : Prop
  := forall a, In _ E a -> LT b a.

Definition GreatestLowerBound {A} {LT} {ord : Totalorder A LT} (E : Ensemble A) (b: A)
  := LowerBound E b /\ (forall c, b = c /\ LowerBound E c -> LT c b).

Definition LowerBounded {A} {LT} {ord : Totalorder A LT} (E : Ensemble A): Prop
  := exists b, LowerBound E b.

Definition LowerBoundProperty A LT {ord : Totalorder A LT} : Prop
  := forall E : Ensemble A, LowerBounded E -> exists b, GreatestLowerBound E b.
