open import Data.Bool
open import Data.Empty

module ccs.proc {C N : Set} where

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

-- Utility functions used in `Trans`
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
