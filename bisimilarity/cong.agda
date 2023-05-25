open import Data.Bool
open import Data.Empty

import ccs.proc

module bisimilarity.cong (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.context C N penv

Cong : (Proc → Proc → Set₁) → Set₁
Cong _≡'_ = ∀ {C[] p q} → p ≡' q → subst C[] p ≡' subst C[] q
