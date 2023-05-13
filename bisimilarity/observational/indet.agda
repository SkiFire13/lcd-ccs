{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Bool
open import Data.Product

import ccs.proc

module bisimilarity.observational.indet {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.cong {C} {N} {penv}
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.strong.base {C} {N} {penv}
open import bisimilarity.strong.congruence {C} {N} {penv} renaming (cong to ~-cong)
open import bisimilarity.strong.properties {C} {N} {penv} using () renaming (reflexive to ~-refl)
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.congruence {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv} using (p≈p+d) renaming (reflexive to ≈-refl; sym to ≈-sym; trans to ≈-trans)

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

cong : Cong _≈ᵢ_
p-to-q (closure (cong p≈ᵢq) r) (indet {q = r'} {s = false} t) =
  r' , trans-to-weak (indet t) , ≈-refl
p-to-q (closure (cong {chan c C[]} {q = q} p≈ᵢq) r) (indet {s = true} chan) =
  subst C[] q , trans-to-weak (indet chan) , ≈ᵢ-to-≈ (cong p≈ᵢq)
p-to-q (closure (cong {par-L C[] pc} {q = q} p≈ᵢq) r) (indet {s = true} t) with t
... | par-L tl = {!   !}
... | par-R {p' = pc'} tr =
  par (subst C[] q) pc' , trans-to-weak (indet (par-R tr)) , par-respects-≈ (≈ᵢ-to-≈ (cong {C[]} p≈ᵢq)) ≈-refl
... | par-B tl tr = {!   !}
p-to-q (closure (cong {par-R pc C[]} p≈ᵢq) r) (indet {s = true} t) = {!   !}
p-to-q (closure (cong {indet C[] pc} p≈ᵢq) r) t =
  ≈-trans (≈-trans helper (cong p≈ᵢq .closure (indet₂ pc r))) (≈-sym helper) .p-to-q t
  where
  helper : forall {p1 p2 p3} -> indet₂ (indet₂ p1 p2) p3 ≈ indet₂ p1 (indet₂ p2 p3)
  p-to-q helper (indet {s = true} (indet {s = true} t)) = -, trans-to-weak (indet t) , ≈-refl
  p-to-q helper (indet {s = true} (indet {s = false} t)) = -, trans-to-weak (indet (indet t)), ≈-refl
  p-to-q helper (indet {s = false} t) = -, trans-to-weak (indet (indet t)) , ≈-refl
  q-to-p helper (indet {s = true} t) = -, trans-to-weak (indet (indet t)) , ≈-refl
  q-to-p helper (indet {s = false} (indet {s = true} t)) = -, trans-to-weak (indet (indet t)) , ≈-refl
  q-to-p helper (indet {s = false} (indet {s = false} t)) = -, trans-to-weak (indet t), ≈-refl
p-to-q (closure (cong {rename f C[]} p≈ᵢq) r) (indet {s = true} t) = {!   !}
p-to-q (closure (cong {hide f C[]} p≈ᵢq) r) (indet {s = true} (hide {z = z} t)) with
  cong {C[]} p≈ᵢq .closure ccs.deadlock .p-to-q (indet {s = true} t)
... | foo = {!   !}
-- ... | q' , send self (indet {s = true} tq) s2 , p'≈q' =
--   hide f q' , send self (indet (hide {z = z} tq)) (s-map hide s2), hide-respects-≈ p'≈q'
-- ... | _ , send self (indet {s = false} (indet {s = ()} _)) _ , _
-- ... | q' , send (cons (indet {s = true} tq) s1) tq' s2 , p'≈q' =
--   hide f q' , send (cons (indet (hide tq)) (s-map hide s1)) (hide {z = z} tq') (s-map hide s2), hide-respects-≈ p'≈q'
-- ... | _ , send (cons (indet {s = false} (indet {s = ()} _)) _) _ _ , _
-- ... | q' , recv self (indet {s = true} tq) s2 , p'≈q' =
--   hide f q' , recv self (indet (hide {z = z} tq)) (s-map hide s2), hide-respects-≈ p'≈q'
-- ... | _ , recv self (indet {s = false} (indet {s = ()} _)) _ , _
-- ... | q' , recv (cons (indet {s = true} tq) s1) tq' s2 , p'≈q' =
--   hide f q' , recv (cons (indet (hide tq)) (s-map hide s1)) (hide {z = z} tq') (s-map hide s2), hide-respects-≈ p'≈q'
-- ... | _ , recv (cons (indet {s = false} (indet {s = ()} _)) _) _ _ , _
-- ... | q' , tau (cons (indet {s = true} tq) s) , p'≈q' =
--   hide f q' , tau (cons (indet (hide tq)) (s-map hide s)) , hide-respects-≈ p'≈q'
-- ... | _ , tau (cons (indet {s = false} (indet {s = ()} _)) _) , _
-- ... | q' , tau self , p'≈q' = {!   !}
p-to-q (closure (cong {replace} p≈ᵢq) r) (indet {s = true} t) = p≈ᵢq .closure r .p-to-q (indet t)
q-to-p (closure (cong p≈ᵢq) r) = cong (sym p≈ᵢq) .closure r .p-to-q
