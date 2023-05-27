open import Base

module ccs.proc (C N : Set) where

-- An action
data Act : Set where
  send  : C → Act
  recv  : C → Act
  τ   : Act

-- A CCS Process
data Proc : Set₁ where
  chan    : Act → Proc → Proc
  par     : Proc → Proc → Proc
  indet   : {S : Set} → (S → Proc) → Proc
  const   : N → Proc
  rename  : (C → C) → Proc → Proc
  hide    : Filter C → Proc → Proc

-- The desugaring of the deadlock CCS Process
deadlock = indet ⊥-elim

-- A non-deterministic choice with 2 possible choices

data Indet₂ : Set where
  left right : Indet₂

_+_ : Proc → Proc → Proc
p + q = indet {Indet₂} λ { left → p ; right → q }

infixl 6 _+_

-- Utility functions used for transitions

flip-act : Act → Act
flip-act (send c) = recv c
flip-act (recv c) = send c
flip-act τ        = τ

map-act : (C → C) → (Act → Act)
map-act f (send c) = send (f c)
map-act f (recv c) = recv (f c)
map-act f τ        = τ

filter-act : Filter C → Filter Act
filter-act f (send c) = f c
filter-act f (recv c) = f c
filter-act f τ        = T

-- The type of a process environment
PEnv : Set₁
PEnv = N → Proc
