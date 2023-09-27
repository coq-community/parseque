From parseque Require Import Indexed Sized.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import PeanoNat.

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

Definition le_lift {m n : nat} (p : m <= n) (s : Success Toks Tok A m) :
  Success Toks Tok A n :=
  let small := Nat.le_trans _ _ _  (small s) p
  in MkSuccess (value s) small (leftovers s).

Definition lt_lift {m n : nat} (p : m < n) (s : Success Toks Tok A m) :
  Success Toks Tok A n := le_lift (Nat.lt_le_incl _ _ p) s.

Definition fromView : View Toks Tok n -> Success Toks Tok Tok n :=
match n return View Toks Tok n -> Success Toks Tok Tok n with
  | O    => False_rect _
  | S n' => uncurry (fun t ts => MkSuccess t (Nat.le_refl _) ts)
end.

End Success.

Section Success2.

Context
  {Toks : nat -> Type} {Tok : Type} `{Sized Toks Tok}
  {A B : Type} {n : nat}.

Definition and (p : Success Toks Tok A n) (q : Success Toks Tok B (size p)) :
  Success Toks Tok (A * B) n :=
  lt_lift (small p) (map (fun v => (value p, v)) q).

Definition getTok (ts : Toks n) : option (Success Toks Tok Tok n) :=
  option_map fromView (uncons ts).

End Success2.
