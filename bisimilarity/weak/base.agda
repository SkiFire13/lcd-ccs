{-# OPTIONS --guardedness #-}

open import Data.Product

import ccs.proc

module bisimilarity.weak.base (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv

-- (Half) the property of a weak bisimulation
BisimulationProperty : (Proc → Proc → Set₁) → Proc → Proc → Set₁
BisimulationProperty R p q = ∀ {a p'} → (p -[ a ]→ p') → ∃[ q' ] ((q =[ a ]⇒ q') × R p' q')

-- Weak bisimilarity defined coinductively
record _≈_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : BisimulationProperty _≈_ p q
    q-to-p : BisimulationProperty _≈_ q p
open _≈_ public
infixl 5 _≈_
