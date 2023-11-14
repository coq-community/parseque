From parseque Require Import Indexed.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Le.
Require Import PeanoNat.


Record Box (A : nat -> Type) (n : nat) : Type :=
  MkBox { call : forall m, m < n -> A m }.

Arguments call {_} {_} _ {_}.
Arguments MkBox {_} {_}.

Section Induction.

Context {A B C : nat -> Type}.

Definition map (f : [ A :-> B ]) : [ Box A :-> Box B ] :=
  fun _ b => MkBox (fun _ mltn => f _ (call b mltn)).

Definition map2 (f : [ A :-> B :-> C ]) : [ Box A :-> Box B :-> Box C ] :=
 fun _ a b => MkBox (fun m mltn => f _ (call a mltn) (call b mltn)).

Definition app : [ Box (A :-> B) :-> Box A :-> Box B ] :=
  fun _ f a => MkBox (fun m mltn => call f mltn (call a mltn)).

Definition extract (v : [ Box A ]) : [ A ] :=
  fun _ => call (v _) (le_n _).

Definition duplicate : [ Box A :-> Box (Box A) ] :=
  fun n v => MkBox (fun m mltn =>
             MkBox (fun p pltm =>
  let mltp := Nat.lt_trans _ _ _ pltm mltn
  in call v mltp)).

Definition FixBox (alg : [ Box A :-> A ]) : [ Box A ] :=
fix rec n := match n with
 | O    => MkBox (fun m mltO => False_rect _ (Nat.nlt_0_r _ mltO))
 | S n' => MkBox (fun m mltn => alg _
          (MkBox (fun p pltm =>
             let mltn' := Nat.le_trans _ _ _ pltm (le_S_n _ _ mltn)
             in call (rec n') mltn')))
end.

Definition le_close (down : forall m n, m <= n -> A n -> A m) : [ A :-> Box A ] :=
  fun _ a => MkBox (fun m mltn => down _ _ (Nat.lt_le_incl _ _ mltn) a).

Definition le_lower {m n : nat} (mlen : m <= n) (b : Box A n) : Box A m :=
  MkBox (fun p pltm => call b (Nat.le_trans _ _ _ pltm mlen)).

Definition lt_lower {m n : nat} (mltn : m < n) (b : Box A n) : Box A m :=
  MkBox (fun p pltm => call b (Nat.lt_trans _ _ _ pltm mltn)).

End Induction.

Definition Fix A (alg : [ Box A :-> A ]) : [ A ] := extract (FixBox alg).

Definition Loeb A : [ Box (Box A :-> A) :-> Box A ] :=
  Fix _ (fun _ r alg => app _ alg (app _ r (duplicate _ alg))).
