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

-- Utility functions used in `Reduc`
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
data Reduc {penv : PEnv} : Proc -> Act -> Proc -> Set₁ where
  chan    : forall {c p}
            -> Reduc (chan c p) c p
  par-L   : forall {c pl pr p'}
            -> Reduc {penv} pl c p'
            -> Reduc (par pl pr) c (par p' pr)
  par-R   : forall {c pl pr p'}
            -> Reduc {penv} pr c p' 
            -> Reduc (par pl pr) c (par pl p')
  par-B   : forall {c pl pr pl' pr'}
            -> Reduc {penv} pl c pl'
            -> Reduc {penv} pr (flip-act c) pr'
            -> Reduc (par pl pr) tau (par pl' pr')
  indet   : forall {S} {c q f}
            -> {s : S}
            -> Reduc {penv} (f s) c q
            -> Reduc (indet f) c q
  const   : forall {c p n}
            -> Reduc {penv} (penv n) c p
            -> Reduc (const n) c p
  rename  : forall {c p q r}
            -> Reduc {penv} p c q
            -> Reduc (rename r p) (map-action r c) (rename r q)
  hide    : forall {c p q f}
            -> {z : T (filter-act f c)}
            -> Reduc {penv} p c q
            -> Reduc (hide f p) c (hide f q)
