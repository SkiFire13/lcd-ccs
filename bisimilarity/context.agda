{-# OPTIONS --safe #-}

open import Base

import ccs.proc

module bisimilarity.context (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv hiding (deadlock)

-- A CCS process context with a single hole
data Context : Set₁ where
  chan   : Act → Context → Context
  par    : Context → Proc → Context
  indet  : Context → Proc → Context
  rename : (C → C) → Context → Context
  hide   : Filter C → Context → Context
  hole   : Context

-- Replaces a context hole with a process
subst : Context → Proc → Proc
subst (chan a C[])   p = chan a (subst C[] p)
subst (par C[] q)    p = par (subst C[] p) q
subst (indet C[] q)  p = subst C[] p + q
subst (rename f C[]) p = rename f (subst C[] p)
subst (hide f C[])   p = hide f (subst C[] p)
subst hole           p = p

-- Composes two contexts
compose : Context → Context → Context
compose (chan a C₁[])   C₂[] = chan a (compose C₁[] C₂[])
compose (par C₁[] q)    C₂[] = par (compose C₁[] C₂[]) q
compose (indet C₁[] q)  C₂[] = indet (compose C₁[] C₂[]) q
compose (rename f C₁[]) C₂[] = rename f (compose C₁[] C₂[])
compose (hide f C₁[])   C₂[] = hide f (compose C₁[] C₂[])
compose hole            C₂[] = C₂[]

-- The type of a witness of a bisimilarity being a congruence
Cong : (Proc → Proc → Set₁) → Set₁
Cong _≡ₓ_ = ∀ {C[] p q} → p ≡ₓ q → subst C[] p ≡ₓ subst C[] q
