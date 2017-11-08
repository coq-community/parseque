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

Arguments MkRawAlternative {_} {_} {_}.

Class RawMonad (F : Type -> Type) `{RawApplicative F} :=
  MkRawMonad { _bind : forall A B, F A -> (A -> F B) -> F B }.

Definition bind {F : Type -> Type} `{RawMonad F} {A B : Type} : F A -> (A -> F B) -> F B :=
  _bind _ _.

Arguments MkRawMonad {_} {_} {_}.

Require Import Coq.Lists.List.

Instance listRawFunctor : RawFunctor list :=
  MkRawFunctor map.

Instance listRawApplicative : RawApplicative list :=
  MkRawApplicative (fun _ x => cons x nil) (fun _ _ fs xs => flat_map (fun f => map f xs) fs).

Instance listRawAlternative : RawAlternative list :=
  MkRawAlternative (@nil) (fun _ xs ys => xs ++ ys).

Instance listRawMonad : RawMonad list :=
  MkRawMonad (fun _ _ xs f => flat_map f xs).