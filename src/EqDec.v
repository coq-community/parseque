Class EqDec (A : Type) := MkEqDec { eq_dec : forall (a b : A), { a = b } + { a <> b } }.

Arguments MkEqDec {_}.

From Coq Require Import PeanoNat.
#[global]
Instance natEqDec : EqDec nat := MkEqDec Nat.eq_dec.

From Coq Require Import Ascii.
#[global]
Instance asciiEqDec : EqDec ascii := MkEqDec ascii_dec.

