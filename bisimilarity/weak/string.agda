{-# OPTIONS --guardedness #-}

open import Data.Product

import ccs.proc

module bisimilarity.weak.string {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.weak.base {C} {N} {penv}

-- (Half) the property of a weak string bisimulation
StringBisimulationProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
StringBisimulationProperty R p q = forall {a p'} -> WeakTrans p a p' -> ∃[ q' ] (WeakTrans q a q' × R p' q')

-- Weak bisimilarity defined coinductively
record _≈ₛ_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : StringBisimulationProperty _≈ₛ_ p q
    q-to-p : StringBisimulationProperty _≈ₛ_ q p
open _≈ₛ_ public

-- Weak string bisimilarity implies weak bisimilarity
≈ₛ-to-≈ : forall {p q} -> p ≈ₛ q -> p ≈ q
p-to-q (≈ₛ-to-≈ p≈ₛq) t =
  let q' , t' , p'≈ₛq' = p≈ₛq .p-to-q (trans-to-weak t)
  in q' , t' , ≈ₛ-to-≈ p'≈ₛq'
q-to-p (≈ₛ-to-≈ p≈ₛq) t =
  let p' , t' , q'≈ₛp' = p≈ₛq .q-to-p (trans-to-weak t)
  in p' , t' , ≈ₛ-to-≈ q'≈ₛp'

-- Weak bisimilarity implies weak string bisimilarity
≈-to-≈ₛ : forall {p q} -> p ≈ q -> p ≈ₛ q
q-to-p (≈-to-≈ₛ p≈q) = p-to-q (≈-to-≈ₛ record { p-to-q = p≈q .q-to-p ; q-to-p = p≈q .p-to-q })
p-to-q (≈-to-≈ₛ p≈q) t = let q' , t' , p'≈q' = p-to-q-weak p≈q t in q' , t' , ≈-to-≈ₛ p'≈q'
  where
  p-to-q-tau : forall {p q p'} -> p ≈ q -> TauSeq p p' -> ∃[ q' ] (WeakTrans q tau q' × p' ≈ q')
  p-to-q-tau {q = q} p≈q self = q , tau self , p≈q
  p-to-q-tau {q = q} p≈q (cons t s') =
    let q1 , r1 , p'≈q1 = p≈q .p-to-q t
        q2 , r2 , p'≈q2 = p-to-q-tau p'≈q1 s'
    in q2 , join-tau r1 r2 , p'≈q2

  p-to-q-split : forall {p1 p2 p3 p4 q a} -> p1 ≈ q -> TauSeq p1 p2 -> Trans p2 a p3 -> TauSeq p3 p4
               -> ∃[ q' ] (WeakTrans q a q' × p4 ≈ q')
  p-to-q-split p≈q s1 t s2 =
    let q1 , r1 , p'≈q1 = p-to-q-tau p≈q s1
        q2 , r2 , p'≈q2 = p'≈q1 .p-to-q t
        q3 , r3 , p'≈q3 = p-to-q-tau p'≈q2 s2
    in q3 , join r1 r2 r3 , p'≈q3
  p-to-q-weak : forall {p q a p'} -> p ≈ q -> WeakTrans p a p' -> ∃[ q' ] (WeakTrans q a q' × p' ≈ q')
  p-to-q-weak p≈q (send s1 t s2) = p-to-q-split p≈q s1 t s2
  p-to-q-weak p≈q (recv s1 t s2) = p-to-q-split p≈q s1 t s2
  p-to-q-weak p≈q (tau s) = p-to-q-tau p≈q s
