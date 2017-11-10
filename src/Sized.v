Require Import PeanoNat.

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
  | S n' => fun vw => prod_curry (f _) vw
end.

Require Import Vector.

Instance sizedVector {A : Type} : Sized (Vector.t A) A :=
  MkSized (fun n => match n return Vector.t A n -> option (View (Vector.t A) A n) with
    | O    => fun _ => None
    | S n' => fun v => Some (hd v, tl v)
  end).

Require Import Ascii.
Require Import String.

Record SizedType {A : Type} (size : A -> nat) (n : nat) : Type :=
  MkSizedType { value : A
           ; sized : size value = n
           }.

Arguments MkSizedType {_} {_} {_}.

Definition SizedString n := SizedType length n.

Definition mkString (str : string) : SizedString (length str) := MkSizedType str (eq_refl _).

Definition stringUncons {n} (Str : SizedString (S n)) : ascii * SizedString n :=
  let (str, prf) := Str in
  (match str return length str = S n -> ascii * SizedString n with
   | EmptyString => fun hf  => False_rect _ (Nat.neq_0_succ _ hf)
   | String c s' => fun Seq => pair c (MkSizedType s' (Nat.succ_inj _ _ Seq))
  end) prf.

Instance sizedString : Sized SizedString ascii := MkSized (fun n =>
match n return SizedString n -> option (View _ _ n) with
 | O    => fun _   => None
 | S n' => fun str => Some (stringUncons str)
end).