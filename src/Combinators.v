Require Import Coq.Arith.Le.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.PeanoNat.
Require Import Induction.
Require Import Sized.
Require Import Success.
Require Import EqDec.
Require Import NEList.
Require Import Category.

Record Parser (Toks : nat -> Type) (Tok : Type)
              (M : Type -> Type) (A : Type) (n : nat) : Type :=
  MkParser { runParser {m} : m <= n -> Toks m -> M (Success Toks Tok A m) }.

Arguments MkParser {_} {_} {_} {_} {_}.
Arguments runParser {_} {_} {_} {_} {_} _ {_}.

Section Lower.

Context
  {Toks : nat -> Type} {Tok : Type}
  {M : Type -> Type}
  {A : Type} {m n : nat}.

Definition le_lower (mlen : m <= n) (p : Parser Toks Tok M A n) : Parser Toks Tok M A m :=
  MkParser (fun _ plem => runParser p (le_trans _ _ _ plem mlen)).

Definition lt_lower (mltn : m < n) (p : Parser Toks Tok M A n) : Parser Toks Tok M A m :=
  le_lower (Nat.lt_le_incl _ _ mltn) p.

End Lower.

Definition box {Toks Tok M A n} : Parser Toks Tok M A n -> Box (Parser Toks Tok M A) n :=
  le_close (fun _ _ => le_lower) _.

Coercion box : Parser >-> Box.

Section Combinators1.

Context
  {Toks : nat -> Type} {Tok : Type} `{Sized Toks Tok}
  {M : Type -> Type} `{RawFunctor M} `{RawApplicative M} `{RawMonad M} `{RawAlternative M}
  {A B : Type} {n : nat}.

Definition anyTok : Parser Toks Tok M Tok n :=
 MkParser (fun m mlen ts => fromOption (getTok ts)).

Definition guardM (f : A -> option B) (p : Parser Toks Tok M A n) :
  Parser Toks Tok M B n :=
  MkParser (fun _ mlen toks =>
            bind (runParser p mlen toks) (fun s =>
            fromOption (Success.guardM f s))).

Definition map (f : A -> B) (p : Parser Toks Tok M A n) :
  Parser Toks Tok M B n := MkParser (fun _ mlen toks =>
  fmap (Success.map f) (runParser p mlen toks)).

Definition cmap (b : B) (p : Parser Toks Tok M A n) : Parser Toks Tok M B n :=
  map (fun _ => b) p.

Definition fail : Parser Toks Tok M A n := MkParser (fun _ _ _ => fail).

Definition alt (p q : Parser Toks Tok M A n) : Parser Toks Tok M A n :=
  MkParser (fun _ mlen toks =>
  alt (runParser p mlen toks) (runParser q mlen toks)).

Definition alts (ps : list (Parser Toks Tok M A n)) : Parser Toks Tok M A n :=
  List.fold_right alt fail ps.

Definition andmbind (p : Parser Toks Tok M A n)
  (q : A -> Box (Parser Toks Tok M B) n) : Parser Toks Tok M (A * option B) n :=
  MkParser (fun _ mlen ts => bind (runParser p mlen ts) (fun sa =>
  let salen   := lt_le_trans _ _ _ (small sa) mlen in
  let combine := fun sb => Success.map (fun p => (fst p, Some (snd p))) (Success.and sa sb) in
  Category.alt (fmap combine (runParser (call (q (value sa)) salen) (le_refl _) (leftovers sa)))
               (pure (Success.map (fun a => (a , None)) sa)))).

(* This could be implemented in terms of andmbind + guardM but for
   efficiency reasons we give a direct implementation *)

Definition andbind (p : Parser Toks Tok M A n)
  (q : A -> Box (Parser Toks Tok M B) n) : Parser Toks Tok M (A * B) n :=
  MkParser (fun _ mlen ts => bind (runParser p mlen ts) (fun sa =>
  let salen  := lt_le_trans _ _ _ (small sa) mlen in
  let adjust := fun sb => Success.map (pair (value sa)) (Success.lt_lift (small sa) sb) in
  fmap adjust (runParser (call (q (value sa)) salen) (le_refl _) (leftovers sa)))).

Definition and (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M (A * B) n := andbind p (fun _ => q).

Definition andm (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M (A * option B) n := andmbind p (fun _ => q).

End Combinators1.

Section Combinators2.

Context
  {Toks : nat -> Type} {Tok : Type} `{Sized Toks Tok}
  {M : Type -> Type} `{RawFunctor M} `{RawApplicative M} `{RawMonad M} `{RawAlternative M}
  {A B : Type} {n : nat}.

Definition mand (p : Parser Toks Tok M A n) (q : Parser Toks Tok M B n) :
  Parser Toks Tok M (option A * B) n :=
  MkParser (fun _ mlen ts => Category.alt
    (runParser (map (fun v => (Some (fst v), snd v)) (and p q)) mlen ts)
    (runParser (map (fun v => (None , v)) q) mlen ts)).

Definition optionTok (f : Tok -> option A) : Parser Toks Tok M A n :=
  guardM f anyTok.

Definition guard (f : A -> bool) (p : Parser Toks Tok M A n) :
  Parser Toks Tok M A n := guardM (fun a => if f a then Some a else None) p.

Definition bind (p : Parser Toks Tok M A n)
  (q : A -> Box (Parser Toks Tok M B) n) : Parser Toks Tok M B n :=
  map snd (andbind p q).

Definition land (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M A n := map fst (and p q).

Definition rand (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M B n := map snd (and p q).

Definition landm (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M A n := map fst (andm p q).

Definition lmand (p : Parser Toks Tok M A n) (q : Parser Toks Tok M B n) :
  Parser Toks Tok M (option A) n := map fst (mand p q).

Definition rmand (p : Parser Toks Tok M A n) (q : Parser Toks Tok M B n) :
  Parser Toks Tok M B n := map snd (mand p q).

Definition randm (p : Parser Toks Tok M A n) (q : Box (Parser Toks Tok M B) n) :
  Parser Toks Tok M (option B) n := map snd (andm p q).

Definition sum (p : Parser Toks Tok M A n) (q : Parser Toks Tok M B n) :
  Parser Toks Tok M (A + B) n := alt (map inl p) (map inr q).

End Combinators2.

Section Combinators3.

Context
  {Toks : nat -> Type} {Tok : Type} `{Sized Toks Tok} `{EqDec Tok}
  {M : Type -> Type} `{RawFunctor M} `{RawApplicative M} `{RawMonad M} `{RawAlternative M}
  {A B C : Type} {n : nat}.

Definition app (p : Parser Toks Tok M (A -> B) n)
  (q : Box (Parser Toks Tok M A) n) : Parser Toks Tok M B n :=
  bind p (fun f => Induction.map (fun _ => map (fun t => f t)) _ q).

Definition exact (t : Tok) : Parser Toks Tok M Tok n :=
  guardM (fun t' => if eq_dec t t' then Some t else None) anyTok.

Definition anyOf (ts : list Tok) : Parser Toks Tok M Tok n :=
  alts (List.map exact ts).

Definition exacts (ts : NEList Tok) : Parser Toks Tok M (NEList Tok) n :=
  foldr1 (fun xs ys => map (prod_curry append) (and xs ys))
         (NEList.map (fun t => map singleton (exact t)) ts).

Definition between (open : Parser Toks Tok M A n) (close : Box (Parser Toks Tok M C) n)
  (p : Box (Parser Toks Tok M B) n) : Parser Toks Tok M B n :=
  land (rand open p) close.

Definition betweenm (open : Parser Toks Tok M A n) (close : Box (Parser Toks Tok M C) n)
  (p : Parser Toks Tok M B n) : Parser Toks Tok M B n := landm (rmand open p) close.

End Combinators3.

Section HChainl.

Context
  {Toks : nat -> Type} {Tok : Type}
  {M : Type -> Type} `{RawFunctor M} `{RawApplicative M} `{RawMonad M} `{RawAlternative M}
  {A B : Type} {n : nat}.

Definition LChain (n : nat) : Type :=
  Success Toks Tok A n -> Box (Parser Toks Tok M (A -> A)) n -> M (Success Toks Tok A n).

Definition schainl_aux (n : nat) (rec : Box LChain n) : LChain n := fun sa op =>
  Category.bind (runParser (call op (small sa)) (le_refl _) (leftovers sa)) (fun sop =>
  let sa' := Success.map (fun f => f (value sa)) sop in
  Category.bind (call rec (small sa) sa' (Induction.lt_lower (small sa) op)) (fun res =>
  pure (lt_lift (small sa) res))).

Definition schainl {n : nat} : LChain n :=
  Fix LChain (fun n rec sa op => Category.alt (schainl_aux n rec sa op) (pure sa)) n.

Definition iteratel {n : nat} (val : Parser Toks Tok M A n)
  (op : Box (Parser Toks Tok M (A -> A)) n) : Parser Toks Tok M A n :=
  MkParser (fun _ mlen ts => Category.bind (runParser val mlen ts)
           (fun sa => schainl sa (Induction.le_lower mlen op))).

Definition RChain (n : nat) : Type :=
  Parser Toks Tok M (A -> A) n -> Parser Toks Tok M A n -> Parser Toks Tok M A n.

Definition iterater_aux (n : nat) (rec : Box RChain n) :
  RChain n := fun op val => MkParser (fun _ mlen ts =>
  Category.bind (runParser op mlen ts) (fun sop =>
  let sopltn := lt_le_trans _ _ _ (small sop) mlen in
  let op'    := lt_lower sopltn op in
  let val'   := lt_lower sopltn val in
  Category.bind (runParser (call rec sopltn op' val') (le_refl _) (leftovers sop)) (fun res =>
  pure (lt_lift (small sop) (Success.map (value sop) res))))).

Definition iterater {n : nat} (op : Parser Toks Tok M (A -> A) n)
  (val : Parser Toks Tok M A n) : Parser Toks Tok M A n :=
  Fix _ (fun n rec op val => alt (iterater_aux n rec op val) val) n op val.

Definition hchainl {n : nat} (seed : Parser Toks Tok M A n)
  (op : Box (Parser Toks Tok M (A -> B -> A)) n)
  (arg : Box (Parser Toks Tok M B) n) : Parser Toks Tok M A n :=
  let op'  := Induction.map (fun _ => map (fun f b a => f a b)) _ op in
  let arg' := duplicate _ arg in
  iteratel seed (map2 (fun _ => app) _ op' arg').

End HChainl.

Section Chains.

Context
  {Toks : nat -> Type} {Tok : Type}
  {M : Type -> Type} `{RawFunctor M} `{RawApplicative M} `{RawMonad M} `{RawAlternative M}
  {A B : Type} {n : nat}.

Definition chainl1 (p : Parser Toks Tok M A n)
  (op : Box (Parser Toks Tok M (A -> A -> A)) n) : Parser Toks Tok M A n :=
  hchainl p op p.

Definition nelist : Parser Toks Tok M A n -> Parser Toks Tok M (NEList A) n :=
  Fix _ (fun _ rec p => map (prod_curry consm)
        (andmbind p (fun _ => Induction.app _ rec p))) _.

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


