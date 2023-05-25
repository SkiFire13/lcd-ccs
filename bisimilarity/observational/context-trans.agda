{-# OPTIONS --guardedness #-}

open import Data.Product

import ccs.proc

module bisimilarity.observational.context-trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.context C N penv
open import bisimilarity.observational.context C N penv renaming (sym to ̂≈-sym)
open import bisimilarity.observational.trans C N penv renaming (cong to ≈ₒ-cong)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv renaming (sym to ≈-sym; trans to ≈-trans)

≈ₒ→̂≈ : ∀ {p q} → p ≈ₒ q → p ̂≈ q
≈ₒ→̂≈ p≈ₒq = ≈-cong→̂≈ ≈ₒ→≈ ≈ₒ-cong p≈ₒq

̂≈→≈ₒ : (c : C) → ∀ {p q} → p ̂≈ q → p ≈ₒ q
p⇒q (̂≈→≈ₒ c (obs-c C[p]≈C[q])) {a = send _} t with C[p]≈C[q] C[] .p⇒q (indet t)
  where C[] = indet replace ccs.deadlock
... | q' , send self (indet {s = left} tq) s2 , p'≈q' = q' , obs-t self tq s2 , p'≈q'
... | _ , send self (indet {s = right} (indet {s = ()} _)) _ , _
... | q' , send (cons (indet {s = left} tq) s1) tq' s2 , p'≈q' = q' , obs-t (cons tq s1) tq' s2 , p'≈q'
... | _ , send (cons (indet {s = right} (indet {s = ()} _)) _) _ _ , _
p⇒q (̂≈→≈ₒ c (obs-c C[p]≈C[q])) {a = recv _} t with C[p]≈C[q] C[] .p⇒q (indet t)
  where C[] = indet replace ccs.deadlock
... | q' , recv self (indet {s = left} tq) s2 , p'≈q' = q' , obs-t self tq s2 , p'≈q'
... | _ , recv self (indet {s = right} (indet {s = ()} _)) _ , _
... | q' , recv (cons (indet {s = left} tq) s1) tq' s2 , p'≈q' = q' , obs-t (cons tq s1) tq' s2 , p'≈q'
... | _ , recv (cons (indet {s = right} (indet {s = ()} _)) _) _ _ , _
p⇒q (̂≈→≈ₒ c (obs-c C[p]≈C[q])) {a = tau} t = {!   !}
q⇒p (̂≈→≈ₒ c oc) = ̂≈→≈ₒ c (̂≈-sym oc) .p⇒q
