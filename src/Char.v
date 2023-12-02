From parseque Require Import Category Induction Combinators Sized NEList Numbers.
From Coq Require Import Ascii String.
From parseque Require Import StringAsList.
From Coq Require Import List.
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

Definition alpha : Parser Chars ascii M ascii n :=
  anyOf (fromString "abcdefghijklmnopqrstuvwxyz"%string).

Definition num : Parser Chars ascii M nat n := decimal_digit.

Definition alphanum : Parser Chars ascii M (ascii + nat) n :=
  sum alpha num.

End Char.
