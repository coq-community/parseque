Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.PeanoNat.
Require Import Induction.
Require Import Sized.
Require Import Success.
Require Import EqDec.
Require Import Category.

Record Parser (Toks : nat -> Type) (Tok : Type)
              (M : Type -> Type) (A : Type) (n : nat) : Type :=
  MkParser { runParser {m} : m <= n -> Toks m -> M (Success Toks Tok A m) }.

Arguments MkParser {_} {_} {_} {_} {_}.
Arguments runParser {_} {_} {_} {_} {_} _ {_}.

Definition box {Toks Tok M A n} : Parser Toks Tok M A n -> Box (Parser Toks Tok M A) n :=
  le_close (fun _ _ mlen p => MkParser (fun _ llem ts =>
    let mlep := le_trans _ _ _ llem mlen
    in runParser p mlep ts)) _.

Coercion box : Parser >-> Box.

Section Combinators1.

Context {Toks : nat -> Type} {Tok : Type} {M : Type -> Type} {A B : Type} {n : nat}.

Definition anyTok `{RawAlternative M} `{Sized Toks Tok} : Parser Toks Tok M Tok n :=
 MkParser (fun m mlen ts => fromOption (getTok ts)).

Definition guardM `{RawAlternative M} `{RawMonad M} (f : A -> option B)
  (p : Parser Toks Tok M A n) : Parser Toks Tok M B n :=
  MkParser (fun _ mlen toks =>
            bind (runParser p mlen toks) (fun s =>
            fromOption (Success.guardM f s))).

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

Program Definition alts `{RawAlternative M} (ps : list (Parser Toks Tok M A n)) :
  Parser Toks Tok M A n := List.fold_right alt fail ps.

Definition andmbind `{RawAlternative M} `{RawMonad M} (p : Parser Toks Tok M A n)
  (q : A -> Box (Parser Toks Tok M B) n) : Parser Toks Tok M (A * option B) n :=
  MkParser (fun _ mlen ts => bind (runParser p mlen ts) (fun sa =>
  let salen   := lt_le_trans _ _ _ (small sa) mlen in
  let combine := fun sb => Success.map (fun p => (fst p, Some (snd p))) (Success.and sa sb) in
  Category.alt (fmap combine (runParser (call (q (value sa)) salen) (le_refl _) (leftovers sa)))
               (pure (Success.map (fun a => (a , None)) sa)))).

(* This could be implemented in terms of andmbind + guardM but for
   efficiency reasons we give a direct implementation *)

Definition andbind `{RawMonad M} (p : Parser Toks Tok M A n)
  (q : A -> Box (Parser Toks Tok M B) n) : Parser Toks Tok M (A * B) n :=
  MkParser (fun _ mlen ts => bind (runParser p mlen ts) (fun sa =>
  let salen  := lt_le_trans _ _ _ (small sa) mlen in
  let adjust := fun sb => Success.map (pair (value sa)) (Success.lt_lift (small sa) sb) in
  fmap adjust (runParser (call (q (value sa)) salen) (le_refl _) (leftovers sa)))).

Definition and `{RawMonad M} (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M (A * B) n := andbind p (fun _ => q).

Definition andm `{RawAlternative M} `{RawMonad M} (p : Parser Toks Tok M A n)
  (q : Box (Parser Toks Tok M B) n) : Parser Toks Tok M (A * option B) n :=
  andmbind p (fun _ => q).

End Combinators1.

Section Combinators2.

Context {Toks : nat -> Type} {Tok : Type} {M : Type -> Type} {A B : Type} {n : nat}.

Definition mand `{RawAlternative M} `{RawMonad M} (p : Parser Toks Tok M A n)
  (q : Parser Toks Tok M B n) : Parser Toks Tok M (option A * B) n :=
  MkParser (fun _ mlen ts => Category.alt
    (runParser (map (fun v => (Some (fst v), snd v)) (and p q)) mlen ts)
    (runParser (map (fun v => (None , v)) q) mlen ts)).

Definition optionTok `{RawAlternative M} `{RawMonad M} `{Sized Toks Tok}
  (f : Tok -> option A) : Parser Toks Tok M A n :=
  guardM f anyTok.

Definition guard `{RawAlternative M} `{RawMonad M} (f : A -> bool)
  (p : Parser Toks Tok M A n) : Parser Toks Tok M A n :=
  guardM (fun a => if f a then Some a else None) p.

Definition bind `{RawMonad M} (p : Parser Toks Tok M A n)
  (q : A -> Box (Parser Toks Tok M B) n) : Parser Toks Tok M B n :=
  map snd (andbind p q).

Definition land `{RawMonad M} (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M A n := map fst (and p q).

Definition rand `{RawMonad M} (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M B n := map snd (and p q).

Definition landm `{RawAlternative M} `{RawMonad M} (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M A n := map fst (andm p q).

Definition lmand `{RawAlternative M} `{RawMonad M} (p : Parser Toks Tok M A n) (q : Parser Toks Tok M B n) :
  Parser Toks Tok M (option A) n := map fst (mand p q).

Definition rmand `{RawAlternative M} `{RawMonad M} (p : Parser Toks Tok M A n) (q : Parser Toks Tok M B n) :
  Parser Toks Tok M B n := map snd (mand p q).

Definition randm `{RawAlternative M} `{RawMonad M} (p : Parser Toks Tok M A n)
  (q : Box (Parser Toks Tok M B) n) : Parser Toks Tok M (option B) n := map snd (andm p q).

Definition sum `{RawAlternative M} (p : Parser Toks Tok M A n) (q : Parser Toks Tok M B n) :
  Parser Toks Tok M (A + B) n := alt (map inl p) (map inr q).

End Combinators2.

Section Combinators3.

Context {Toks : nat -> Type} {Tok : Type} {M : Type -> Type} {A B C : Type} {n : nat}.

Definition app `{RawMonad M} (p : Parser Toks Tok M (A -> B) n)
  (q : Box (Parser Toks Tok M A) n) : Parser Toks Tok M B n :=
  bind p (fun f => Induction.map (fun _ => map (fun t => f t)) _ q).

Definition exact `{RawAlternative M} `{RawMonad M} `{Sized Toks Tok} `{EqDec Tok} (t : Tok)
  : Parser Toks Tok M Tok n := guardM (fun t' => if eq_dec t t' then Some t else None) anyTok.

Definition anyOf `{RawAlternative M} `{RawMonad M} `{Sized Toks Tok} `{EqDec Tok}
  (ts : list Tok) : Parser Toks Tok M Tok n := alts (List.map exact ts).

Definition between `{RawMonad M} (open : Parser Toks Tok M A n) (close : Box (Parser Toks Tok M C) n)
  (p : Box (Parser Toks Tok M B) n) : Parser Toks Tok M B n :=
  land (rand open p) close.

Definition betweenm `{RawAlternative M} `{RawMonad M} (open : Parser Toks Tok M A n)
  (close : Box (Parser Toks Tok M C) n) (p : Parser Toks Tok M B n) : Parser Toks Tok M B n :=
  landm (rmand open p) close.

End Combinators3.

Section HChainl.

Context {Toks : nat -> Type} {Tok : Type} {M : Type -> Type} {A B : Type}.

Definition LChain (n : nat) : Type :=
  Success Toks Tok A n -> Box (Parser Toks Tok M (A -> A)) n -> M (Success Toks Tok A n).

Definition schainl_aux `{RawMonad M}
  (n : nat) (rec : Box LChain n) : LChain n := fun sa op =>
  Category.bind (runParser (call op (small sa)) (le_refl _) (leftovers sa)) (fun sop =>
  pure (Success.map (fun f => f (value sa)) (lt_lift (small sa) sop))).

Definition schainl `{RawAlternative M} `{RawMonad M} {n : nat} : LChain n :=
  Fix LChain (fun n rec sa op => Category.alt (schainl_aux n rec sa op) (pure sa)) n.

Definition iteratel `{RawMonad M} `{RawAlternative M} {n} (val : Parser Toks Tok M A n)
  (op : Box (Parser Toks Tok M (A -> A)) n) : Parser Toks Tok M A n :=
  MkParser (fun _ mlen ts => Category.bind (runParser val mlen ts)
           (fun sa => schainl sa (le_lower mlen op))).

Definition hchainl `{RawMonad M} `{RawAlternative M} {n}
  (seed : Parser Toks Tok M A n) (op : Box (Parser Toks Tok M (A -> B -> A)) n)
  (arg : Box (Parser Toks Tok M B) n) : Parser Toks Tok M A n :=
  let op'  := Induction.map (fun _ => map (fun f b a => f a b)) _ op in
  let arg' := duplicate _ arg in
  iteratel seed (map2 (fun _ => app) _ op' arg').

End HChainl.

Section Chains.

Context {Toks : nat -> Type} {Tok : Type} {M : Type -> Type} {A : Type} {n : nat}.

Definition chainl1 `{RawMonad M} `{RawAlternative M} (p : Parser Toks Tok M A n)
  (op : Box (Parser Toks Tok M (A -> A -> A)) n) : Parser Toks Tok M A n :=
  hchainl p op p.

End Chains.



(* TODO: fix the fixity levels *)
Notation "p <|> q"   := (alt p q)  (at level 40, left associativity).
Notation "f <$> p"   := (map f p)  (at level 60, right associativity).
Notation "b <$ p"    := (cmap b p) (at level 60, right associativity).
Notation "p &?>>= q" := (andmbind p q) (at level 60, right associativity).
Notation "p &>>= q"  := (andbind p q)  (at level 60, right associativity).
Notation "p >>= q"   := (bind p q)     (at level 60, right associativity).
Notation "p <&> q"   := (and p q)      (at level 60, right associativity).
Notation "p <&  q"   := (land p q)     (at level 60, right associativity).
Notation "p  &> q"   := (rand p q)     (at level 60, right associativity).
Notation "p <&?> q"  := (andm p q)     (at level 60, right associativity).
Notation "p <&? q"   := (landm p q)    (at level 60, right associativity).
Notation "p &?> q"   := (randm p q)    (at level 60, right associativity).
Notation "p <?&> q"  := (mand p q)     (at level 60, right associativity).
Notation "p <?& q"   := (lmand p q)    (at level 60, right associativity).
Notation "p ?&> q"   := (rmand p q)    (at level 60, right associativity).
Notation "p <*> q"   := (app p q)      (at level 60, right associativity).
Notation "p <+> q"   := (sum p q)      (at level 60, right associativity).


