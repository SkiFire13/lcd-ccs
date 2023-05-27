{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.strong.base (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv

-- Strong bisimilarity defined coinductively
-- Note: q' ~ p' is not faithful to the original definition, but is more ergonomic for proofs.
--       See correct-order for the proof that they are equivalent.
record _~_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p⇒q : ∀ {a p'} → (p -[ a ]→ p') → ∃[ q' ] (q -[ a ]→ q' × p' ~ q')
    q⇒p : ∀ {a q'} → (q -[ a ]→ q') → ∃[ p' ] (p -[ a ]→ p' × q' ~ p')
open _~_ public
infixl 5 _~_
