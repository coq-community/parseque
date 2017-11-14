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

Context
  {Chars : nat -> Type} `{Sized Chars ascii}
  {M : Type -> Type} `{RawFunctor M} `{RawApplicative M} `{RawMonad M} `{RawAlternative M}
  {A : Type} {n : nat}.

Definition char (c : ascii) : Parser Chars ascii M ascii n := exact c.

Definition space : Parser Chars ascii M ascii n :=
  anyOf (" " :: "009" :: "013" :: [])%char.

Definition spaces : Parser Chars ascii M (NEList ascii) n := nelist space.

Definition text (t : String) `{NonEmpty ascii t} : Parser Chars ascii M String n :=
  Combinators.map NEList.toList (exacts nonEmpty).

Definition parens (p : Box (Parser Chars ascii M A) n) : Parser Chars ascii M A n :=
  between (char "(") (char ")") p.

Definition parensm (p : Parser Chars ascii M A n) : Parser Chars ascii M A n :=
  betweenm (char "(") (char ")") p.

Definition withSpaces (p : Parser Chars ascii M A n) : Parser Chars ascii M A n :=
  spaces ?&> p <&? spaces.

End Char.