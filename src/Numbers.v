From parseque Require Import Category Sized NEList Combinators.
From Coq Require Import Ascii.
Local Open Scope char.
From Coq Require Import List.
Import ListNotations.
From Coq Require Import BinInt.

Section Numbers.

Context
  {M : Type -> Type} `{RawFunctor M} `{RawApplicative M} `{RawMonad M} `{RawAlternative M}
  {Chars : nat -> Type} `{Sized Chars ascii}
  {n : nat}.

Definition decimal_digit : Parser Chars ascii M nat n :=
  alts ((0 <$ exact "0")
     :: (1 <$ exact "1")
     :: (2 <$ exact "2")
     :: (3 <$ exact "3")
     :: (4 <$ exact "4")
     :: (5 <$ exact "5")
     :: (6 <$ exact "6")
     :: (7 <$ exact "7")
     :: (8 <$ exact "8")
     :: (9 <$ exact "9")
     :: []).

Definition decimal_nat : Parser Chars ascii M nat n :=
  let convert ds := foldl (fun ih d => 10 * ih + d) ds O
  in Combinators.map convert (nelist decimal_digit).

Definition decimal_int : Parser Chars ascii M Z n :=
  let convert s v := option_rect _ (fun _ => Z.opp) (fun x => x) s (Z.of_nat v)
  in Combinators.map (uncurry convert) (exact "-" <?&> decimal_nat).

End Numbers.


