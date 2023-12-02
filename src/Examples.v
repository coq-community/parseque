From parseque Require Import Running Parseque.
From Coq Require Import Ascii String.

Section ArithmeticLanguage.

Context
  {Toks : nat -> Type} `{Sized Toks ascii}
  {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

Inductive Expr : Type :=
  | EEmb : Term -> Expr
  | EAdd : Expr -> Term -> Expr
  | ESub : Expr -> Term -> Expr
with Term : Type :=
  | TEmb : Factor -> Term
  | TMul : Term -> Factor -> Term
  | TDiv : Term -> Factor -> Term
with Factor : Type :=
  | FEmb : Expr -> Factor
  | FLit : nat -> Factor
.

Record Language (n : nat) : Type := MkLanguage
  { _expr   : Parser Toks ascii M Expr n
  ; _term   : Parser Toks ascii M Term n
  ; _factor : Parser Toks ascii M Factor n
  }.

Arguments MkLanguage {_}.

Definition language : [ Language ] := Fix Language (fun _ rec =>
  let addop  := EAdd <$ char "+" <|> ESub <$ char "-" in
  let mulop  := TMul <$ char "*" <|> TDiv <$ char "/" in
  let factor := FEmb <$> parens (Induction.map _expr _ rec) <|> FLit <$> decimal_nat in
  let term   := hchainl (TEmb <$> factor) mulop factor in
  let expr   := hchainl (EEmb <$> term) addop term in
  MkLanguage expr term factor).

Definition expr   : [ Parser Toks ascii M Expr   ] := fun n => _expr n (language n).
Definition term   : [ Parser Toks ascii M Term   ] := fun n => _term n (language n).
Definition factor : [ Parser Toks ascii M Factor ] := fun n => _factor n (language n).

End ArithmeticLanguage.

Local Open Scope string_scope.

Definition test1 : check "1+1" expr := MkSingleton
  (EAdd (EEmb (TEmb (FLit 1)))
              (TEmb (FLit 1))).

Definition test2 : check "1+(2*31-4)" expr := MkSingleton
 (EAdd (EEmb (TEmb (FLit 1)))
             (TEmb (FEmb (ESub (EEmb (TMul (TEmb (FLit 2)) (FLit 31)))
                                           (TEmb (FLit 4)))))).
