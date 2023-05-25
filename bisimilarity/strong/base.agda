{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.strong.base (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv

-- (Half) the property of a strong bisimulation
BisimulationProperty : (Proc → Proc → Set₁) → Proc → Proc → Set₁
BisimulationProperty _R_ p q = ∀ {a p'} → (p -[ a ]→ p') → ∃[ q' ] ((q -[ a ]→ q') × p' R q')

-- Strong bisimilarity defined coinductively
record _~_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p⇒q : BisimulationProperty _~_ p q
    q⇒p : BisimulationProperty _~_ q p
open _~_ public
infixl 5 _~_
