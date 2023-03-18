module ccs (C N : Set) where
-- C = Channel, N = Name (Constant)

open import Data.Bool
open import Data.Empty

data ChanOp : Set where
  send  : C -> ChanOp
  recv  : C -> ChanOp
  tau   : ChanOp

flip-chan-op : ChanOp -> ChanOp
flip-chan-op (send c) = recv c
flip-chan-op (recv c) = send c
flip-chan-op tau = tau

map-chan-op : (C -> C) -> ChanOp -> ChanOp
map-chan-op f (send c) = send (f c)
map-chan-op f (recv c) = recv (f c)
map-chan-op f tau = tau

filter-chan-op : (C -> Bool) -> ChanOp -> Bool
filter-chan-op f (send c) = f c
filter-chan-op f (recv c) = f c
filter-chan-op f tau = true

data Prog : Set₁ where
  chan    : ChanOp -> Prog -> Prog
  par     : Prog -> Prog -> Prog
  indet   : {S : Set} -> (S -> Prog) -> Prog
  const   : N -> Prog
  rename  : (C -> C) -> Prog -> Prog
  hide    : (C -> Bool) -> Prog -> Prog

deadlock = indet ⊥-elim

variable
  F : N -> Prog
-- F = Function (from constant to the associated program)
data Reduces : Prog -> ChanOp -> Prog -> Set₁ where
  chan    : forall {c p} -> Reduces (chan c p) c p
  par-L   : forall {c pl pr p'} -> Reduces pl c p' -> Reduces (par pl pr) c (par p' pr)
  par-R   : forall {c pl pr p'} -> Reduces pr c p' -> Reduces (par pl pr) c (par pl p')
  par-B   : forall {c pl pr pl' pr'} -> Reduces pl c pl' -> Reduces pr (flip-chan-op c) pr'
            -> Reduces (par pl pr) tau (par pl' pr')
  indet   : forall {S} {c q f} {s : S} -> Reduces (f s) c q -> Reduces (indet f) c q
  const   : forall {c p n} -> Reduces (F n) c p -> Reduces (const n) c p
  rename  : forall {c p q r} -> Reduces p c q -> Reduces (rename r p) (map-chan-op r c) (rename r q)
  hide    : forall {c p q f} {_ : T (filter-chan-op f c)} -> Reduces p c q -> Reduces (hide f p) c (hide f q)
 