Require Import Indexed.
Require Import Sized.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.

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

Context {Toks : nat -> Type} {Tok : Type} {A B C : Type} {n : nat}.

Definition map (f : A -> B) : Success Toks Tok A n -> Success Toks Tok B n :=
  fun s => MkSuccess (f (value s)) (small s) (leftovers s).

Definition guardM (f : A -> option B) : Success Toks Tok A n -> option (Success Toks Tok B n) :=
  fun s => option_map (fun b => MkSuccess b (small s) (leftovers s)) (f (value s)).

Definition lift {m n : nat} (p : m <= n) (s : Success Toks Tok A m) :
                Success Toks Tok A n :=
  let small := le_trans _ _ _  (small s) p
  in MkSuccess (value s) small (leftovers s).

Definition and (p : Success Toks Tok A n) (q : Success Toks Tok B (size p)) :
  Success Toks Tok (A * B) n :=
  MkSuccess (value p, value q) (lt_trans _ _ _ (small q) (small p)) (leftovers q).

Definition fromView : View Toks Tok n -> Success Toks Tok Tok n :=
match n return View Toks Tok n -> Success Toks Tok Tok n with
  | O    => False_rect _
  | S n' => prod_curry (fun t ts => MkSuccess t (le_refl _) ts)
end.

End Success.

Definition getTok {Toks} {Tok} `{Sized Toks Tok} {n} : Toks n -> option (Success Toks Tok Tok n) :=
  fun ts => option_map fromView (uncons ts).