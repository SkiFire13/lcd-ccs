open import Data.Bool
open import Data.Empty

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
module ccs {C N : Set} where

-- A channel operation
data ChanOp : Set where
  send  : C -> ChanOp
  recv  : C -> ChanOp
  tau   : ChanOp

-- A CCS Process
data Proc : Set₁ where
  chan    : ChanOp -> Proc -> Proc
  par     : Proc -> Proc -> Proc
  indet   : {S : Set} -> (S -> Proc) -> Proc
  const   : N -> Proc
  rename  : (C -> C) -> Proc -> Proc
  hide    : (C -> Bool) -> Proc -> Proc

-- The "desugaring" of the deadlock CCS Process
deadlock = indet ⊥-elim

-- Utility functions used in `Reduces`
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

-- A relation of reduction between two CCS processes with a channel operation.
-- It is also parameterized over the process environment (`penv`), that is the
-- mapping from the name of constants to their process.
-- (For technical reasons this can't be included in the process type itself)
data Reduces {penv : N -> Proc} : Proc -> ChanOp -> Proc -> Set₁ where
  chan    : forall {c p} -> Reduces (chan c p) c p
  par-L   : forall {c pl pr p'} -> Reduces {penv} pl c p' -> Reduces (par pl pr) c (par p' pr)
  par-R   : forall {c pl pr p'} -> Reduces {penv} pr c p' -> Reduces (par pl pr) c (par pl p')
  par-B   : forall {c pl pr pl' pr'} -> Reduces {penv} pl c pl' -> Reduces {penv} pr (flip-chan-op c) pr'
            -> Reduces (par pl pr) tau (par pl' pr')
  indet   : forall {S} {c q f} {s : S} -> Reduces {penv} (f s) c q -> Reduces (indet f) c q
  const   : forall {c p n} -> Reduces {penv} (penv n) c p -> Reduces (const n) c p
  rename  : forall {c p q r} -> Reduces {penv} p c q -> Reduces (rename r p) (map-chan-op r c) (rename r q)
  hide    : forall {c p q f} {z : T (filter-chan-op f c)} -> Reduces {penv} p c q -> Reduces (hide f p) c (hide f q)
