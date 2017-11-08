Require Import Indexed.
Require Import Sized.
Require Import Success.
Require Import Category.

Record Parser (Toks : nat -> Type) (Tok : Type)
              (M : Type -> Type) (A : Type) (n : nat) : Type :=
  MkParser { runParser : forall m, m <= n -> Toks m -> M (Success Toks Tok A m) }.

Arguments MkParser {_} {_} {_} {_} {_}.
Arguments runParser {_} {_} {_} {_} {_} _ {_}.

Section Parser.

Variable (Toks : nat -> Type).
Variable (Tok : Type).
Variable (M : Type -> Type).

Definition anyTok `{RawAlternative M} `{Sized Toks Tok} : [ Parser Toks Tok M Tok ] :=
 fun n => MkParser (fun m mlen ts =>
 match getTok _ ts with
  | None   => fail
  | Some t => pure t
 end).

End Parser.