Class RawFunctor (F : Type -> Type) :=
  MkRawFunctor { _fmap : forall A B, (A -> B) -> (F A -> F B)
               }.

Definition fmap {F : Type -> Type} `{RawFunctor F} {A B : Type} : (A -> B) -> (F A -> F B) :=
  _fmap _ _.

Arguments MkRawFunctor {_}.

Class RawApplicative (F : Type -> Type) `{RawFunctor F} :=
  MkRawApplicative { _pure       : forall A, A -> F A
                   ; _app        : forall A B, F (A -> B) -> (F A -> F B)
                   }.


Definition pure {F : Type -> Type} `{RawApplicative F} {A : Type} : A -> F A :=
  _pure _.

Definition app {F : Type -> Type} `{RawApplicative F} {A B : Type} : F (A -> B) -> (F A -> F B) :=
  _app _ _.

Arguments MkRawApplicative {_} {_}.

Class RawAlternative (F : Type -> Type) `{RawApplicative F} :=
  MkRawAlternative { _fail : forall A, F A
                   ; _alt  : forall A, F A -> F A -> F A
                   }.

Definition fail {F : Type -> Type} `{RawAlternative F} {A : Type} : F A :=
  _fail _.

Definition alt {F : Type -> Type} `{RawAlternative F} {A : Type} : F A -> F A -> F A :=
  _alt _.

Definition fromOption {F : Type -> Type} `{RawAlternative F} {A : Type} (v : option A) : F A :=
match v with
 | None   => fail
 | Some a => pure a
end.

Arguments MkRawAlternative {_} {_} {_}.

Class RawMonad (F : Type -> Type) `{RawApplicative F} :=
  MkRawMonad { _bind : forall A B, F A -> (A -> F B) -> F B }.

Definition bind {F : Type -> Type} `{RawMonad F} {A B : Type} :
  F A -> (A -> F B) -> F B := _bind _ _.

Fixpoint mapM {M : Type -> Type} `{RawMonad M} {A B : Type}
 (f : A -> M B) (xs : list A) : M (list B) :=
match xs with
  | nil        => pure nil
  | cons x xs' => bind (f x) (fun fx => fmap (cons fx) (mapM f xs'))
end.

Arguments MkRawMonad {_} {_} {_}.

Class RawMonadRun (F : Type -> Type) `{RawMonad F} :=
  MkRawMonadRun { _runMonad : forall A, F A -> list A }.

Definition runMonad {F : Type -> Type} `{RawMonadRun F} {A : Type} : F A -> list A := _runMonad _.

Arguments MkRawMonadRun {_} {_} {_} {_}.

Require Import Coq.Lists.List.

Instance listRawFunctor : RawFunctor list :=
  MkRawFunctor map.

Instance listRawApplicative : RawApplicative list :=
  MkRawApplicative (fun _ x => cons x nil) (fun _ _ fs xs => flat_map (fun f => map f xs) fs).

Instance listRawAlternative : RawAlternative list :=
  MkRawAlternative (@nil) (fun _ xs ys => xs ++ ys).

Instance listRawMonad : RawMonad list :=
  MkRawMonad (fun _ _ xs f => flat_map f xs).

Instance listRawMonadRun : RawMonadRun list :=
  MkRawMonadRun (fun _ x => x).


Instance optionRawFunctor : RawFunctor option :=
  MkRawFunctor option_map.

Instance optionRawApplicative : RawApplicative option :=
  MkRawApplicative (fun _ => Some) (fun A B => option_rect _ (option_map (B := B)) (fun _ => None)).

Instance optionRawAlternative : RawAlternative option :=
  MkRawAlternative (@None) (fun _ => option_rect _ (fun x _ => Some x) (fun x => x)).

Instance optionRawMonad : RawMonad option :=
  MkRawMonad (fun _ _ xs f => option_rect _ f None xs).

Instance optionRawMonadRun : RawMonadRun option :=
  MkRawMonadRun (fun _ => option_rect _ (fun x => cons x nil) nil).