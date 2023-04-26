{-# OPTIONS --guardedness #-}

open import Data.Product

import ccs.proc

module bisimilarity.weak.strong {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.strong.properties {C} {N} {penv}
open import bisimilarity.strong.base {C} {N} {penv}

~-to-≈ : forall {p q} -> p ~ q -> p ≈ q
p-to-q (~-to-≈ p~q) t =
  let q' , t' , p'~q' = p~q .p-to-q t
  in q' , trans-to-weak t' , ~-to-≈ p'~q'
q-to-p (~-to-≈ p~q) = p-to-q (~-to-≈ (sym p~q))
