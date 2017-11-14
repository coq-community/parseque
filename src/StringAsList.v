Require Import Ascii.
Require Import String.

Require Import Coq.Lists.List.
Import ListNotations.

Definition String := list ascii.

Fixpoint fromString (s : string) : String :=
match s with
 | String.EmptyString => []
 | String.String c s' => c :: fromString s'
end.

Fixpoint toString (s : String) : string :=
  fold_right String.String String.EmptyString s.