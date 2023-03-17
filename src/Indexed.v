Section Indexed.

Local Open Scope type.

Context {I : Type} (T : Type) (A B : I -> Type).

Definition IArrow : I -> Type :=
  fun i => A i -> B i.

Definition ISum : I -> Type :=
  fun i => A i + B i.

Definition IProduct : I -> Type :=
  fun i => A i * B i.

Definition IConstant : I -> Type :=
  fun i => T.

Definition ICompose (T : Type -> Type) : I -> Type :=
  fun i => T (A i).

Definition IForall : Type :=
  forall {i}, A i.

End Indexed.

Notation "T :o A"  := (ICompose A T) (at level 10).
Notation "A :-> B" := (IArrow A B)   (at level 20, right associativity).
Notation "A :+  B" := (ISum A B)     (at level 30).
Notation "A :*  B" := (IProduct A B) (at level 40).
Notation ":K A"    := (IConstant A)  (at level 50).
Notation "[ A ]"   := (IForall A)    (at level 70).
