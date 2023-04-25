open import Data.Bool
open import Data.Product
open import Relation.Nullary

import ccs.proc

module bisimilarity.weak.congruence {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv} as ctx
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv}

-- Prove that ≈ is not a congruence
≈-not-cong : {c : C} -> ¬ forall {C[] p q} -> p ≈ q -> subst C[] p ≈ subst C[] q
≈-not-cong {c} cong with cong {C[]} τd≈d .p-to-q (indet {s = true} chan)
  where
  τd≈d : chan tau ccs.deadlock ≈ ccs.deadlock
  p-to-q τd≈d chan = ccs.deadlock , tau self , reflexive
  q-to-p τd≈d (indet {s = ()} _)
  C[] = indet \ b -> if b then replace else chan (send c) ctx.deadlock
... | _ , tau (cons (indet {s = true} (indet {s = ()} _)) _) , _
... | _ , tau self , d≈c[d] with d≈c[d] .q-to-p (indet {s = false} chan)
...   | _ , send self (indet {s = ()} _) _ , _
...   | _ , send (cons (indet {s = ()} _) _) _ _ , _
