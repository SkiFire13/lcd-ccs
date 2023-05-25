{-# OPTIONS --guardedness #-}

open import Data.Product

import ccs.proc

module bisimilarity.weak.correct-order (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv

-- Weak bisimilarity defined coinductively
record _≈ₒ_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : ∀ {a p'} → (p -[ a ]→ p') → ∃[ q' ] ((q =[ a ]⇒ q') × p' ≈ₒ q')
    q-to-p : ∀ {a q'} → (q -[ a ]→ q') → ∃[ p' ] ((p =[ a ]⇒ p') × p' ≈ₒ q')
open _≈ₒ_ public

-- Prove symmetry for _≈ₒ_ because otherwise Agda termination checker will fail in the next theorem
≈ₒ-sym : ∀ {p q} → p ≈ₒ q → q ≈ₒ p
p-to-q (≈ₒ-sym p≈ₒq) t =
  let p' , t' , p'≈ₒq' = p≈ₒq .q-to-p t
  in p' , t' , ≈ₒ-sym p'≈ₒq'
q-to-p (≈ₒ-sym p≈ₒq) t =
  let q' , t' , p'≈ₒq' = p≈ₒq .p-to-q t
  in q' , t' , ≈ₒ-sym p'≈ₒq'

-- Weak bisimilarity implies weak bisimilarity (with the correct order)
≈-to-≈ₒ : ∀ {p q} → p ≈ q → p ≈ₒ q
p-to-q (≈-to-≈ₒ p≈q) t =
  let q' , t' , p'≈q' = p≈q .p-to-q t
  in q' , t' , ≈-to-≈ₒ p'≈q'
q-to-p (≈-to-≈ₒ p≈q) t =
  let p' , t' , q'≈p' = p≈q .q-to-p t
  in p' , t' , ≈-to-≈ₒ (sym q'≈p')
-- Weak bisimilarity (with the correct order) implies weak bisimilarity
≈ₒ-to-≈ : ∀ {p q} → p ≈ₒ q → p ≈ q
p-to-q (≈ₒ-to-≈ p≈ₒq) t =
  let q' , t' , p'≈ₒq' = p≈ₒq .p-to-q t
  in q' , t' , ≈ₒ-to-≈ p'≈ₒq'
q-to-p (≈ₒ-to-≈ p≈ₒq) t = 
  let q' , t' , p'≈ₒq' = p≈ₒq .q-to-p t
  in q' , t' , ≈ₒ-to-≈ (≈ₒ-sym p'≈ₒq')
