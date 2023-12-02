From Coq Require Import PeanoNat.

Definition View (As : nat -> Type) (A : Type) (n : nat) : Type :=
match n with
  | O    => False
  | S n' => A * As n'
end.

Class Sized As A : Type := MkSized { uncons {n} : As n -> option (View As A n) }.

Arguments MkSized {_} {_}.

Definition view {As A B} (f : forall n, A -> As n -> B (S n)) {n : nat} : View As A n -> B n :=
match n return View As A n -> B n with
  | O    => fun hf => False_rect _ hf
  | S n' => fun vw => uncurry (f _) vw
end.

From Coq Require Import Vector.

#[global]
Instance sizedVector {A : Type} : Sized (Vector.t A) A :=
  MkSized (fun n => match n return Vector.t A n -> option (View (Vector.t A) A n) with
    | O    => fun _ => None
    | S n' => fun v => Some (hd v, tl v)
  end).

Record SizedType {A : Type} (size : A -> nat) (n : nat) : Type :=
  MkSizedType { value : A
              ; sized : size value = n
              }.

Arguments MkSizedType {_} {_} {_}.

From Coq Require Import List.
Import ListNotations.

Definition SizedList (A : Type) n := SizedType (@length A) n.

Section SizedList.

Context {A : Type}.

Definition mkSizedList (xs : list A) : SizedList A (length xs) :=
  MkSizedType xs (eq_refl _).

Definition listUncons {n : nat} (xs : SizedList A (S n)) : A * SizedList A n :=
  let (vs, prf) := xs in
  (match vs return length vs = S n -> A * SizedList A n with
   | []       => fun hf  => False_rect _ (Nat.neq_0_succ _ hf)
   | v :: vs' => fun Seq => pair v (MkSizedType vs' (Nat.succ_inj _ _ Seq))
  end) prf.

End SizedList.

#[global]
Instance sizedList : forall (A : Type), Sized (SizedList A) A :=
fun A => MkSized (fun n =>
match n return SizedList A n -> option (View _ _ n) with
 | O    => fun _   => None
 | S n' => fun str => Some (listUncons str)
end).
