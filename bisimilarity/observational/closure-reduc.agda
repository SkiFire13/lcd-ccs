{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

import ccs.proc

module bisimilarity.observational.closure-reduc {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.observational.closure {C} {N} {penv} renaming (sym to ̂≈-sym)
open import bisimilarity.observational.reduc {C} {N} {penv} renaming (sym to ≈ₒ-sym)
open import bisimilarity.weak.base {C} {N} {penv}

̂≈-to-≈ₒ : (c : C) -> forall {p q} -> p ̂≈ q -> p ≈ₒ q
p-to-q (̂≈-to-≈ₒ c (closure C[p]≈C[q])) {a = send _} t with C[p]≈C[q] C[] .p-to-q (indet t)
  where C[] = indet replace ccs.deadlock
... | q' , send self (indet {s = true} tq) s2 , p'≈q' = q' , obs-t self tq s2 , p'≈q'
... | _ , send self (indet {s = false} (indet {s = ()} _)) _ , _
... | q' , send (cons (indet {s = true} tq) s1) tq' s2 , p'≈q' = q' , obs-t (cons tq s1) tq' s2 , p'≈q'
... | _ , send (cons (indet {s = false} (indet {s = ()} _)) _) _ _ , _
p-to-q (̂≈-to-≈ₒ c (closure C[p]≈C[q])) {a = recv _} t with C[p]≈C[q] C[] .p-to-q (indet t)
  where C[] = indet replace ccs.deadlock
... | q' , recv self (indet {s = true} tq) s2 , p'≈q' = q' , obs-t self tq s2 , p'≈q'
... | _ , recv self (indet {s = false} (indet {s = ()} _)) _ , _
... | q' , recv (cons (indet {s = true} tq) s1) tq' s2 , p'≈q' = q' , obs-t (cons tq s1) tq' s2 , p'≈q'
... | _ , recv (cons (indet {s = false} (indet {s = ()} _)) _) _ _ , _
p-to-q (̂≈-to-≈ₒ c (closure C[p]≈C[q])) {a = tau} t with C[p]≈C[q] C[] .p-to-q (indet (hide t))
  where C[] = indet (hide (\ _ -> false) replace) (chan (send c) ccs.deadlock)
... | q' , tau (cons tq s) , p'≈q' = {!   !}
... | q' , tau self , p'≈q' with p'≈q' .q-to-p (indet {s = false} chan)
... | q'' , send s1 tq _ , _ = ⊥-elim (helper s1 tq)
  where
  helper : forall {p1 p2 p3} -> TauSeq (hide (\ _ -> false) p1) p2 -> Trans p2 (send c) p3 -> ⊥
  helper (cons (hide t') s1) tq' = helper s1 tq'
  helper self (hide {z = ()} _)
q-to-p (̂≈-to-≈ₒ c oc) = ̂≈-to-≈ₒ c (̂≈-sym oc) .p-to-q
