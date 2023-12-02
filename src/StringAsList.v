From Coq Require Import Ascii String List.
Import ListNotations.

Definition String := list ascii.

Fixpoint fromString (s : string) : String :=
match s with
 | String.EmptyString => []
 | String.String c s' => c :: fromString s'
end.

Definition toString (s : String) : string :=
  fold_right String.String String.EmptyString s.
