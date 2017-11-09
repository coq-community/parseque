Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.PeanoNat.
Require Import Induction.
Require Import Sized.
Require Import Success.
Require Import Category.

Record Parser (Toks : nat -> Type) (Tok : Type)
              (M : Type -> Type) (A : Type) (n : nat) : Type :=
  MkParser { runParser {m} : m <= n -> Toks m -> M (Success Toks Tok A m) }.

Arguments MkParser {_} {_} {_} {_} {_}.
Arguments runParser {_} {_} {_} {_} {_} _ {_}.

Section Combinators1.

Context {Toks : nat -> Type} {Tok : Type} {M : Type -> Type} {A B : Type} {n : nat}.

Definition anyTok `{RawAlternative M} `{Sized Toks Tok} : Parser Toks Tok M Tok n :=
 MkParser (fun m mlen ts => fromOption (getTok ts)).

Definition guardM `{RawAlternative M} `{RawMonad M} (f : A -> option B)
  (p : Parser Toks Tok M A n) : Parser Toks Tok M B n :=
  MkParser (fun _ mlen toks =>
            bind (runParser p mlen toks) (fun s =>
            fromOption (Success.guardM f s))).

Definition box : Parser Toks Tok M A n -> Box (Parser Toks Tok M A) n :=
  le_close (fun _ _ mlen p => MkParser (fun _ llem ts =>
    let mlep := le_trans _ _ _ llem mlen
    in runParser p mlep ts)) _.

Definition map `{RawFunctor M} (f : A -> B) (p : Parser Toks Tok M A n) :
  Parser Toks Tok M B n := MkParser (fun _ mlen toks =>
  fmap (Success.map f) (runParser p mlen toks)).

Definition cmap `{RawFunctor M} (b : B) (p : Parser Toks Tok M A n) :
  Parser Toks Tok M B n := map (fun _ => b) p.

Definition fail `{RawAlternative M} : Parser Toks Tok M A n :=
  MkParser (fun _ _ _ => fail).

Definition alt `{RawAlternative M} (p q : Parser Toks Tok M A n) :
  Parser Toks Tok M A n := MkParser (fun _ mlen toks =>
  alt (runParser p mlen toks) (runParser q mlen toks)).

Definition andmbind `{RawAlternative M} `{RawMonad M} (p : Parser Toks Tok M A n)
  (q : A -> Parser Toks Tok M B n) : Parser Toks Tok M (A * option B) n :=
  MkParser (fun _ mlen ts => bind (runParser p mlen ts) (fun sa =>
  let salen   := le_trans _ _ _ (Nat.lt_le_incl _ _ (small sa)) mlen in
  let combine := fun sb => Success.map (fun p => (fst p, Some (snd p))) (Success.and sa sb) in
  Category.alt (fmap combine (runParser (q (value sa)) salen (leftovers sa)))
               (pure (Success.map (fun a => (a , None)) sa)))).

End Combinators1.

Section Combinators2.

Context {Toks : nat -> Type} {Tok : Type} {M : Type -> Type} {A B : Type} {n : nat}.

Definition optionTok `{RawAlternative M} `{RawMonad M} `{Sized Toks Tok}
  (f : Tok -> option A) : Parser Toks Tok M A n :=
  guardM f anyTok.

Definition guard `{RawAlternative M} `{RawMonad M} (f : A -> bool)
  (p : Parser Toks Tok M A n) : Parser Toks Tok M A n :=
  guardM (fun a => if f a then Some a else None) p.

End Combinators2.

Notation "p <|> q"   := (alt p q)  (at level 40, left associativity).
Notation "f <$> p"   := (map f p)  (at level 60, right associativity).
Notation "b <$ p"    := (cmap b p) (at level 60, right associativity).
Notation "p &?>>= q" := (andmbind p q) (at level 60, right associativity).

Coercion box : Parser >-> Box.
