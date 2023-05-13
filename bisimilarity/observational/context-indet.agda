{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

import ccs.proc

module bisimilarity.observational.context-indet {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.observational.context {C} {N} {penv} renaming (cong to ̂≈-cong; sym to ̂≈-sym)
open import bisimilarity.observational.indet {C} {N} {penv} renaming (cong to ≈ᵢ-cong)
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv} renaming (sym to ≈-sym; trans to ≈-trans)

̂≈-to-≈ᵢ : forall {p q} -> p ̂≈ q -> p ≈ᵢ q
̂≈-to-≈ᵢ (obs-c C[p]≈C[q]) = obs-i \ r -> C[p]≈C[q] (indet replace r)

≈ᵢ-to-̂≈ : forall {p q} -> p ≈ᵢ q -> p ̂≈ q
≈ᵢ-to-̂≈ p≈ᵢq = ≈-cong-to-̂≈ ≈ᵢ-to-≈ ≈ᵢ-cong p≈ᵢq
