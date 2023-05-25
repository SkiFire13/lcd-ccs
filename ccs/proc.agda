open import Data.Empty
open import Data.Unit

module ccs.proc (C N : Set) where

-- An action
data Act : Set where
  send  : C → Act
  recv  : C → Act
  tau   : Act

-- A CCS Process
data Proc : Set₁ where
  chan    : Act → Proc → Proc
  par     : Proc → Proc → Proc
  indet   : {S : Set} → (S → Proc) → Proc
  const   : N → Proc
  rename  : (C → C) → Proc → Proc
  hide    : (C → Set) → Proc → Proc

-- The "desugaring" of the deadlock CCS Process
deadlock = indet ⊥-elim

-- A non-deterministic choice with 2 options
data Indet₂ : Set where
  left right : Indet₂

_+_ : Proc → Proc → Proc
p + q = indet {Indet₂} λ { left → p ; right → q }

infixl 6 _+_

-- Utility functions used in `Trans`
flip-act : Act → Act
flip-act (send c) = recv c
flip-act (recv c) = send c
flip-act tau = tau

map-act : (C → C) → Act → Act
map-act f (send c) = send (f c)
map-act f (recv c) = recv (f c)
map-act f tau = tau

filter-act : (C → Set) → Act → Set
filter-act f (send c) = f c
filter-act f (recv c) = f c
filter-act f tau = ⊤

PEnv : Set₁
PEnv = N → Proc
