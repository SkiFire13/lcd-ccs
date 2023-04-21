open import Data.Bool
open import Data.Empty

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
module ccs {C N : Set} where

-- An action
data Act : Set where
  send  : C -> Act
  recv  : C -> Act
  tau   : Act

-- A CCS Process
data Proc : Set₁ where
  chan    : Act -> Proc -> Proc
  par     : Proc -> Proc -> Proc
  indet   : {S : Set} -> (S -> Proc) -> Proc
  const   : N -> Proc
  rename  : (C -> C) -> Proc -> Proc
  hide    : (C -> Bool) -> Proc -> Proc

-- The "desugaring" of the deadlock CCS Process
deadlock = indet ⊥-elim

-- Utility functions used in `Reduces`
flip-act : Act -> Act
flip-act (send c) = recv c
flip-act (recv c) = send c
flip-act tau = tau

map-action : (C -> C) -> Act -> Act
map-action f (send c) = send (f c)
map-action f (recv c) = recv (f c)
map-action f tau = tau

filter-act : (C -> Bool) -> Act -> Bool
filter-act f (send c) = f c
filter-act f (recv c) = f c
filter-act f tau = true

PEnv : Set₁
PEnv = N -> Proc

-- A relation of reduction between two CCS processes with a channel operation.
-- It is also parameterized over the process environment (`penv`), that is the
-- mapping from the name of constants to their process.
-- (For technical reasons this can't be included in the process type itself)
data Reduces {penv : PEnv} : Proc -> Act -> Proc -> Set₁ where
  chan    : forall {c p}
            -> Reduces (chan c p) c p
  par-L   : forall {c pl pr p'}
            -> Reduces {penv} pl c p'
            -> Reduces (par pl pr) c (par p' pr)
  par-R   : forall {c pl pr p'}
            -> Reduces {penv} pr c p' 
            -> Reduces (par pl pr) c (par pl p')
  par-B   : forall {c pl pr pl' pr'}
            -> Reduces {penv} pl c pl'
            -> Reduces {penv} pr (flip-act c) pr'
            -> Reduces (par pl pr) tau (par pl' pr')
  indet   : forall {S} {c q f}
            -> {s : S}
            -> Reduces {penv} (f s) c q
            -> Reduces (indet f) c q
  const   : forall {c p n}
            -> Reduces {penv} (penv n) c p
            -> Reduces (const n) c p
  rename  : forall {c p q r}
            -> Reduces {penv} p c q
            -> Reduces (rename r p) (map-action r c) (rename r q)
  hide    : forall {c p q f}
            -> {z : T (filter-act f c)}
            -> Reduces {penv} p c q
            -> Reduces (hide f p) c (hide f q)
