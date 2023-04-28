{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Relation.Binary.PropositionalEquality

import ccs.proc

module bisimilarity.observational.context-trans {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.observational.context {C} {N} {penv} renaming (cong to ̂≈-cong; sym to ̂≈-sym)
open import bisimilarity.observational.trans {C} {N} {penv} renaming (cong to ≈ₒ-cong; sym to ≈ₒ-sym)
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv} renaming (sym to ≈-sym; trans to ≈-trans)

≈ₒ-to-̂≈ : forall {p q} -> p ≈ₒ q -> p ̂≈ q
≈ₒ-to-̂≈ p≈ₒq = obs-c \ _ -> ≈ₒ-to-≈ (≈ₒ-cong p≈ₒq)

̂≈-to-≈ₒ : (c : C) -> forall {p q} -> p ̂≈ q -> p ≈ₒ q
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
p-to-q (̂≈-to-≈ₒ c (obs-c C[p]≈C[q])) {a = tau} t with C[p]≈C[q] C[] .p-to-q (indet t)
  where C[] = indet replace ccs.deadlock
... | _ , tau (cons (indet {s = false} (indet {s = ()} _)) _) , _
... | qd' , tau (cons (indet {s = true} tq) s) , p'≈qd' = qd' , obs-t self tq s , p'≈qd'
... | qd' , tau self , p'≈qd' with C[p]≈C[q] C[] .p-to-q (indet t)
  where C[] = indet replace (chan (send c) ccs.deadlock)
... | _ , tau (cons (indet {s = false} ()) _) , _
... | qc' , tau (cons (indet {s = true} tq) s) , p'≈qc' = qc' , obs-t self tq s , p'≈qc'
... | qc' , tau self , p'≈qc' with C[p]≈C[q] C[] .p-to-q (indet t)
  where C[] = indet replace (chan tau ccs.deadlock)
... | qt' , tau (cons (indet {s = false} chan) (cons (indet {s = ()} _) _)) , p'≈qt'
... | qt' , tau (cons (indet {s = false} chan) self) , p'≈qt' =
  let _ , tqt , _ = ≈-trans (≈-sym p'≈qc') p'≈qt' .p-to-q (indet {s = false} chan)
  in w-deadlock-elim tqt
  where
  w-deadlock-elim : forall {S p} -> WeakTrans ccs.deadlock (send c) p -> S
  w-deadlock-elim (send self (indet {s = ()} _) _)
  w-deadlock-elim (send (cons (indet {s = ()} _) _) _ _)
... | qt' , tau (cons (indet {s = true} tq) s) , p'≈qt' = qt' , obs-t self tq s , p'≈qt'
... | qt' , tau self , p'≈qt' = {!   !}
q-to-p (̂≈-to-≈ₒ c oc) = ̂≈-to-≈ₒ c (̂≈-sym oc) .p-to-q
