open import Base

module ccs-vp.proc (C N X V : Set) (Args : N → Set) where

-- A CCS Value-Passing (VP) Process
data Proc : Set₁ where
  send   : C → V → Proc → Proc
  recv   : C → (V → Proc) → Proc
  tau    : Proc → Proc
  par    : Proc → Proc → Proc
  indet  : {S : Set} → (S → Proc) → Proc
  const  : (n : N) → (Args n) → Proc
  rename : (C → C) → Proc → Proc
  hide   : (Filter C) → Proc → Proc
  if     : Bool → Proc → Proc

-- The desugaring of the deadlock CCS VP Process
deadlock = indet ⊥-elim

-- A CCS VP action
data Act : Set where
  send : C → V → Act
  recv : C → V → Act
  tau  : Act

-- Utility functions used for transitions

flip-act : Act → Act
flip-act (send c v) = recv c v
flip-act (recv c v) = send c v
flip-act tau        = tau

map-act : (C → C) → Act → Act
map-act f (send c v) = send (f c) v
map-act f (recv c v) = recv (f c) v
map-act f tau        = tau

filter-act : (Filter C) → Filter Act
filter-act f (send c _) = f c
filter-act f (recv c _) = f c
filter-act f tau        = T

-- The type of a process environment
PEnv : Set₁
PEnv = (n : N) → (Args n) → Proc
