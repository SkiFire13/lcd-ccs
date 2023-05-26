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
compose (chan a c)   c₂ = chan a (compose c c₂)
compose (par-L c q)  c₂ = par-L (compose c c₂) q
compose (par-R q c)  c₂ = par-R q (compose c c₂)
compose (indet c q)  c₂ = indet (compose c c₂) q
compose (rename f c) c₂ = rename f (compose c c₂)
compose (hide f c)   c₂ = hide f (compose c c₂)
compose replace      c₂ = c₂

-- The type of a witness of a bisimilarity being a congruence
Cong : (Proc → Proc → Set₁) → Set₁
Cong _≡ₓ_ = ∀ {C[] p q} → p ≡ₓ q → subst C[] p ≡ₓ subst C[] q
