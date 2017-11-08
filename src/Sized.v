Require Import Indexed.

Section Sized.

Variable (As : nat -> Type).
Variable (A : Type).

Definition View (n : nat) : Type :=
match n with
  | O    => False
  | S n' => A * As n'
end.

Definition view {B : nat -> Type} (f : forall n, A -> As n -> B (S n)) (n : nat) : View n -> B n :=
match n return View n -> B n with
  | O    => fun hf => False_rect _ hf
  | S n' => fun vw => prod_curry (f _) vw
end.

Class Sized : Type := MkSized { uncons : [ As :-> option :o View ] }.

End Sized.

Arguments view {_} {_} {_} _ {_}.
Arguments MkSized {_} {_}.
Arguments uncons {_} {_} {_} {_}.

Require Import Vector.

Instance sizedVector {A : Type} : Sized (Vector.t A) A :=
  MkSized (fun n => match n return Vector.t A n -> option (View (Vector.t A) A n) with
    | O    => fun _ => None
    | S n' => fun v => Some (hd v, tl v)
  end).