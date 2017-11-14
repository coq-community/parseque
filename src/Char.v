Require Import Category.
Require Import Induction.
Require Import Combinators.
Require Import Sized.
Require Import NEList.

Require Import Ascii.
Require Import StringAsList.

Require Import Coq.Lists.List.
Import ListNotations.

Section Char.

Context {M : Type -> Type} {Chars : nat -> Type} {A : Type} {n : nat}.

Definition char `{RawAlternative M} `{RawMonad M} `{Sized Chars ascii}
  (c : ascii) : Parser Chars ascii M ascii n := exact c.

Definition space `{RawAlternative M} `{RawMonad M} `{Sized Chars ascii}
  : Parser Chars ascii M ascii n := anyOf (" " :: "009" :: "013" :: [])%char.

Definition spaces `{RawAlternative M} `{RawMonad M} `{Sized Chars ascii}
  : Parser Chars ascii M (NEList ascii) n := nelist space.

Definition text `{RawAlternative M} `{RawMonad M} `{Sized Chars ascii}
  (t : String) `{NonEmpty ascii t} : Parser Chars ascii M String n :=
  Combinators.map NEList.toList (exacts nonEmpty).

Definition parens `{RawMonad M} `{RawAlternative M} `{Sized Chars ascii}
  (p : Box (Parser Chars ascii M A) n) : Parser Chars ascii M A n :=
  between (char "(") (char ")") p.

Definition parensm `{RawMonad M} `{RawAlternative M} `{Sized Chars ascii}
  (p : Parser Chars ascii M A n) : Parser Chars ascii M A n :=
  betweenm (char "(") (char ")") p.

Definition withSpaces `{RawMonad M} `{RawAlternative M} `{Sized Chars ascii}
  (p : Parser Chars ascii M A n) : Parser Chars ascii M A n :=
  spaces ?&> p <&? spaces.

End Char.