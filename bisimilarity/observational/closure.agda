{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product

import ccs.proc

module bisimilarity.observational.closure {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.strong.base {C} {N} {penv}
open import bisimilarity.strong.congruence {C} {N} {penv} renaming (cong to ~-cong)
open import bisimilarity.strong.properties {C} {N} {penv} using () renaming (reflexive to ~-refl)
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv} using () renaming (trans to ≈-trans; sym to ≈-sym)
open import bisimilarity.weak.strong {C} {N} {penv} using (~-to-≈)

-- Observational congruence defined as a closure over weak bisimilarity in contexts
data _̂≈_ (p : Proc) (q : Proc) : Set₁ where
  closure : ((C[] : Context) -> (subst C[] p) ≈ (subst C[] q)) -> p ̂≈ q

-- Helper to prove that compose is the same as composing subst under strong bisimilarity
ss~sc : forall {C1[] C2[] p} -> subst C1[] (subst C2[] p) ~ subst (compose C1[] C2[]) p
ss~sc {chan a c} = ~-cong {chan a replace} (ss~sc {c})
ss~sc {par-L c p} = ~-cong {par-L replace p} (ss~sc {c})
ss~sc {par-R p c} = ~-cong {par-R p replace} (ss~sc {c})
p-to-q (ss~sc {indet c _}) (indet {q = p'} {s = s} t) with s
... | true = let q' , t' , p'~q' = ss~sc {c} .p-to-q t in q' , indet t' , p'~q'
... | false = p' , indet {s = false} t , ~-refl
q-to-p (ss~sc {indet c _}) (indet {q = p'} {s = s} t) with s
... | true = let q' , t' , p'~q' = ss~sc {c} .q-to-p t in q' , indet t' , p'~q'
... | false = p' , indet {s = false} t , ~-refl
ss~sc {rename f c} = ~-cong {rename f replace} (ss~sc {c})
ss~sc {hide f c} = ~-cong {hide f replace} (ss~sc {c})
ss~sc {replace} = ~-refl

-- Prove that ̂≈ is a congruence
̂≈-cong : forall {C[] p q} -> p ̂≈ q -> (subst C[] p) ̂≈ (subst C[] q)
̂≈-cong {C[]} {p} {q} (closure C[p]≈C[q]) = closure \ C'[] ->
  let t1 = ~-to-≈ (ss~sc {C'[]} {C[]} {p})
      t2 = C[p]≈C[q] (compose C'[] C[])
      t3 = ~-to-≈ (ss~sc {C'[]} {C[]} {q})
  in ≈-trans (≈-trans t1 t2) (≈-sym t3)
