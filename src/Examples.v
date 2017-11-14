Require Import Parseque.
Require Import Ascii.

Section ArithmeticLanguage.

Context {M : Type -> Type} `{RawMonad M} `{RawAlternative M}.

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
  { expr   : Parser SizedString ascii M Expr n
  ; term   : Parser SizedString ascii M Term n
  ; factor : Parser SizedString ascii M Factor n
  }.

Arguments MkLanguage {_}.

Definition language : [ Language ] := Fix Language (fun _ rec =>
  let addop  := EAdd <$ char "+" <|> ESub <$ char "-" in
  let mulop  := TMul <$ char "*" <|> TDiv <$ char "/" in
  let factor := FEmb <$> parens (Induction.map expr _ rec) <|> FLit <$> decimal_nat in
  let term   := hchainl (TEmb <$> factor) mulop factor in
  let expr   := hchainl (EEmb <$> term) addop term in
  MkLanguage expr term factor).

End ArithmeticLanguage.