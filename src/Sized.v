Require Import Indexed.

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