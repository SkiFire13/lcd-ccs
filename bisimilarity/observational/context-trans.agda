{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

import ccs.proc

module bisimilarity.observational.context-trans {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.observational.context {C} {N} {penv} renaming (sym to ̂≈-sym)
open import bisimilarity.observational.trans {C} {N} {penv} renaming (cong to ≈ₒ-cong)
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv} renaming (sym to ≈-sym; trans to ≈-trans)

≈ₒ-to-̂≈ : ∀ {p q} → p ≈ₒ q → p ̂≈ q
≈ₒ-to-̂≈ p≈ₒq = ≈-cong-to-̂≈ ≈ₒ-to-≈ ≈ₒ-cong p≈ₒq

̂≈-to-≈ₒ : (c : C) → ∀ {p q} → p ̂≈ q → p ≈ₒ q
p-to-q (̂≈-to-≈ₒ c (obs-c C[p]≈C[q])) {a = send _} t with C[p]≈C[q] C[] .p-to-q (indet t)
  where C[] = indet replace ccs.deadlock
... | q' , send self (indet {s = true} tq) s2 , p'≈q' = q' , obs-t self tq s2 , p'≈q'
... | _ , send self (indet {s = false} (indet {s = ()} _)) _ , _
... | q' , send (cons (indet {s = true} tq) s1) tq' s2 , p'≈q' = q' , obs-t (cons tq s1) tq' s2 , p'≈q'
... | _ , send (cons (indet {s = false} (indet {s = ()} _)) _) _ _ , _
p-to-q (̂≈-to-≈ₒ c (obs-c C[p]≈C[q])) {a = recv _} t with C[p]≈C[q] C[] .p-to-q (indet t)
  where C[] = indet replace ccs.deadlock
... | q' , recv self (indet {s = true} tq) s2 , p'≈q' = q' , obs-t self tq s2 , p'≈q'
... | _ , recv self (indet {s = false} (indet {s = ()} _)) _ , _
... | q' , recv (cons (indet {s = true} tq) s1) tq' s2 , p'≈q' = q' , obs-t (cons tq s1) tq' s2 , p'≈q'
... | _ , recv (cons (indet {s = false} (indet {s = ()} _)) _) _ _ , _
p-to-q (̂≈-to-≈ₒ c (obs-c C[p]≈C[q])) {a = tau} t = {!   !}
q-to-p (̂≈-to-≈ₒ c oc) = ̂≈-to-≈ₒ c (̂≈-sym oc) .p-to-q
