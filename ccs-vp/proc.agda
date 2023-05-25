open import Base

module ccs-vp.proc (C N X V : Set) (n-fv : N → Filter X) where

-- A CCS VP Process
data Proc : Set₁ where
  send   : C → V → Proc → Proc
  recv   : C → (V → Proc) → Proc
  tau    : Proc → Proc
  par    : Proc → Proc → Proc
  indet  : {S : Set} → (S → Proc) → Proc
  const  : (n : N) → ((x : X) → {_ : n-fv n x} → V) → Proc
  rename : (C → C) → Proc → Proc
  hide   : (C → Set) → Proc → Proc
  if     : Bool → Proc → Proc

-- The "desugaring" of the deadlock CCS VP Process
deadlock = indet ⊥-elim

-- A CCS VP action. This is a bit different than the CCS's Act
-- in that Processes don't contain channel operations (they are codified in different ways)
-- and this is only used in `Trans`.
data Act : Set where
  send : C → V → Act
  recv : C → V → Act
  tau  : Act

-- Utility functions used in `Trans`
flip-act : Act → Act
flip-act (send c v) = recv c v
flip-act (recv c v) = send c v
flip-act tau = tau

map-act : (C → C) → Act → Act
map-act f (send c v) = send (f c) v
map-act f (recv c v) = recv (f c) v
map-act f tau = tau

filter-act : (C → Set) → Act → Set
filter-act f (send c _) = f c
filter-act f (recv c _) = f c
filter-act f tau = T

PEnv : Set₁
PEnv = (n : N) → ((x : X) → {_ : n-fv n x} → V) → Proc
