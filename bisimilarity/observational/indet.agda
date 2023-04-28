{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product

import ccs.proc

module bisimilarity.observational.indet {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.strong.base {C} {N} {penv}
open import bisimilarity.strong.congruence {C} {N} {penv} renaming (cong to ~-cong)
open import bisimilarity.strong.properties {C} {N} {penv} using () renaming (reflexive to ~-refl)
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.congruence {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv} using (~-to-≈; p≈p+d) renaming (reflexive to ≈-refl; sym to ≈-sym; trans to ≈-trans)

-- Observational congruence defined as a closure over weak bisimilarity in contexts
record _≈ᵢ_ (p : Proc) (q : Proc) : Set₁ where
  constructor obs-i
  field
    closure : (r : Proc) -> indet₂ p r ≈ indet₂ q r
open _≈ᵢ_ public

-- Prove that ≈ᵢ is an equivalence
reflexive : forall {p} -> p ≈ᵢ p
reflexive = obs-i \ _ -> ≈-refl

sym : forall {p q} -> p ≈ᵢ q -> q ≈ᵢ p
sym (obs-i p+r≈q+r) = obs-i \ r -> ≈-sym (p+r≈q+r r)

trans : forall {p q s} -> p ≈ᵢ q -> q ≈ᵢ s -> p ≈ᵢ s
trans (obs-i p+r≈q+r) (obs-i q+r≈s+r) = obs-i \ r -> ≈-trans (p+r≈q+r r) (q+r≈s+r r)

-- Prove that ≈ᵢ implies ≈, even though it is pretty obvious
≈ᵢ-to-≈ : forall {p q} -> p ≈ᵢ q -> p ≈ q
≈ᵢ-to-≈ (obs-i p+r≈q+r) = ≈-trans (≈-trans p≈p+d (p+r≈q+r ccs.deadlock)) (≈-sym p≈p+d)
