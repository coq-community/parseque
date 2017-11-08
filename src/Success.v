Require Import Indexed.
Require Import Sized.
Require Import Coq.Arith.Le.

Record Success (Toks : nat -> Type) (Tok : Type) (A : Type) (n : nat) :=
  MkSuccess { value     : A
            ; size      : nat
            ; small     : size < n
            ; leftovers : Toks size
            }.

Arguments MkSuccess {_} {_} {_} {_} _ {_}.
Arguments value     {_} {_} {_} {_}.
Arguments size      {_} {_} {_} {_}.
Arguments small     {_} {_} {_} {_}.
Arguments leftovers {_} {_} {_} {_}.

Section Success.

Variables (Toks : nat -> Type) (Tok : Type).
Variables (A B C : Type).

Definition map (f : A -> B) : [ Success Toks Tok A :-> Success Toks Tok B ] :=
  fun _ s => MkSuccess (f (value s)) (small s) (leftovers s).

Definition lift {m n : nat} (p : m <= n) (s : Success Toks Tok A m) :
                Success Toks Tok A n :=
  let small := le_trans _ _ _  (small s) p
  in MkSuccess (value s) small (leftovers s).

Definition fromView : [ View Toks Tok :-> Success Toks Tok Tok ] := fun n =>
match n return View Toks Tok n -> Success Toks Tok Tok n with
  | O    => False_rect _
  | S n' => prod_curry (fun t ts => MkSuccess t (le_refl _) ts)
end.

End Success.

Arguments map {_} {_} {_} {_}.
Arguments lift {_} {_} {_} {_} {_}.
Arguments fromView {_} {_}.

Definition getTok {Toks} {Tok} `{Sized Toks Tok} : [ Toks :-> option :o Success Toks Tok Tok ] :=
  fun _ ts => option_map (fromView _) (uncons ts).
