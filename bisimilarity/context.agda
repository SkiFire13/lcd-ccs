open import Base

import ccs.proc

module bisimilarity.context (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv hiding (deadlock)

-- A process context
data Context : Set₁ where
  chan    : Act → Context → Context
  par-L   : Context → Proc → Context
  par-R   : Proc → Context → Context
  indet   : Context → Proc → Context
  rename  : (C → C) → Context → Context
  hide    : (Filter C) → Context → Context
  replace : Context

-- Substitute a process inside a context
subst : Context → Proc → Proc
subst (chan a c)   p = chan a (subst c p)
subst (par-L c q)  p = par (subst c p) q
subst (par-R q c)  p = par q (subst c p)
subst (indet c q)  p = subst c p + q
subst (rename f c) p = rename f (subst c p)
subst (hide f c)   p = hide f (subst c p)
subst replace      p = p

-- Compose two processes in relation to subst
compose : Context → Context → Context
compose (chan a C₁)   C₂ = chan a (compose C₁ C₂)
compose (par-L C₁ q)  C₂ = par-L (compose C₁ C₂) q
compose (par-R q C₁)  C₂ = par-R q (compose C₁ C₂)
compose (indet C₁ q)  C₂ = indet (compose C₁ C₂) q
compose (rename f C₁) C₂ = rename f (compose C₁ C₂)
compose (hide f C₁)   C₂ = hide f (compose C₁ C₂)
compose replace       C₂ = C₂

-- The type of a witness of a bisimilarity being a congruence
Cong : (Proc → Proc → Set₁) → Set₁
Cong _≡ₓ_ = ∀ {C[] p q} → p ≡ₓ q → subst C[] p ≡ₓ subst C[] q
