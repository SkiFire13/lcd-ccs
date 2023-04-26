{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product

import ccs.proc

module bisimilarity.observational.reduc {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv} using () renaming (reflexive to ≈-refl)

-- An observable (weak) transition
data ObsTrans : Proc -> Act -> Proc -> Set₁ where
  obs-t : forall {p1 p2 p3 p4 a} -> TauSeq p1 p2 -> Trans p2 a p3 -> TauSeq p3 p4 -> ObsTrans p1 a p4

trans-to-obs : forall {p a q} -> Trans p a q -> ObsTrans p a q
trans-to-obs t = obs-t self t self

obs-to-weak : forall {p a q} -> ObsTrans p a q -> WeakTrans p a q
obs-to-weak (obs-t s1 t s2) = join (tau s1) (trans-to-weak t) (tau s2)

-- Observational weak bisimilarity property
ObsBisProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
ObsBisProperty R p q = forall {a p'} -> Trans p a p' -> ∃[ q' ] (ObsTrans q a q' × R p' q')

-- Observational congruence defined as weak bisimilarity but with a forced strong transition
record _≈ₒ_ (p : Proc) (q : Proc) : Set₁ where
  field
    p-to-q : ObsBisProperty _≈_ p q
    q-to-p : ObsBisProperty _≈_ q p
open _≈ₒ_

-- Prove that ≈ₒ implies ≈, even though it is pretty obvious
≈ₒ-to-≈ : forall {p q} -> p ≈ₒ q -> p ≈ q
p-to-q (≈ₒ-to-≈ p≈ₒq) t =
  let q' , t' , p'≈q' = p≈ₒq .p-to-q t
  in q' , obs-to-weak t' , p'≈q'
q-to-p (≈ₒ-to-≈ p≈ₒq) t =
  let p' , t' , p'≈q' = p≈ₒq .q-to-p t
  in p' , obs-to-weak t' , p'≈q'

-- Prove that ≈ₒ is an equivalence
reflexive : forall {p} -> p ≈ₒ p
p-to-q reflexive {p' = p'} t = p' , trans-to-obs t , ≈-refl
q-to-p reflexive {p' = p'} t = p' , trans-to-obs t , ≈-refl

sym : forall {p q} -> p ≈ₒ q -> q ≈ₒ p
p-to-q (sym p≈ₒq) = p≈ₒq .q-to-p
q-to-p (sym p≈ₒq) = p≈ₒq .p-to-q

trans : forall {p q s} -> p ≈ₒ q -> q ≈ₒ s -> p ≈ₒ s
p-to-q (trans p≈ₒq q≈ₒs) t =
  let q' , tq , p'≈ₒq' = p≈ₒq .p-to-q t
  in {!   !}
  where
  p-to-q-tau : forall {p q p'} -> p ≈ q -> TauSeq p p' -> ∃[ q' ] (WeakTrans q tau q' × p' ≈ q')
  p-to-q-tau {q = q} p≈q self = q , tau self , p≈q
  p-to-q-tau {q = q} p≈q (cons t s') =
    let q1 , r1 , p'≈q1 = p≈q .p-to-q t
        q2 , r2 , p'≈q2 = p-to-q-tau p'≈q1 s'
    in q2 , join-tau r1 r2 , p'≈q2
q-to-p (trans p≈ₒq q≈ₒs) = p-to-q (trans (sym q≈ₒs) (sym p≈ₒq))
