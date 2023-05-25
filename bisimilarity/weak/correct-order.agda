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
    p⇒q : ∀ {a p'} → (p -[ a ]→ p') → ∃[ q' ] ((q =[ a ]⇒ q') × p' ≈ₒ q')
    q⇒p : ∀ {a q'} → (q -[ a ]→ q') → ∃[ p' ] ((p =[ a ]⇒ p') × p' ≈ₒ q')
open _≈ₒ_ public
infixl 5 _≈ₒ_

-- Prove symmetry for _≈ₒ_ because otherwise Agda termination checker will fail in the next theorem
≈ₒ-sym : ∀ {p q} → p ≈ₒ q → q ≈ₒ p
p⇒q (≈ₒ-sym p≈ₒq) t =
  let p' , t' , p'≈ₒq' = p≈ₒq .q⇒p t
  in p' , t' , ≈ₒ-sym p'≈ₒq'
q⇒p (≈ₒ-sym p≈ₒq) t =
  let q' , t' , p'≈ₒq' = p≈ₒq .p⇒q t
  in q' , t' , ≈ₒ-sym p'≈ₒq'

-- Weak bisimilarity implies weak bisimilarity (with the correct order)
≈→≈ₒ : ∀ {p q} → p ≈ q → p ≈ₒ q
p⇒q (≈→≈ₒ p≈q) t =
  let q' , t' , p'≈q' = p≈q .p⇒q t
  in q' , t' , ≈→≈ₒ p'≈q'
q⇒p (≈→≈ₒ p≈q) t =
  let p' , t' , q'≈p' = p≈q .q⇒p t
  in p' , t' , ≈→≈ₒ (sym q'≈p')
-- Weak bisimilarity (with the correct order) implies weak bisimilarity
≈ₒ→≈ : ∀ {p q} → p ≈ₒ q → p ≈ q
p⇒q (≈ₒ→≈ p≈ₒq) t =
  let q' , t' , p'≈ₒq' = p≈ₒq .p⇒q t
  in q' , t' , ≈ₒ→≈ p'≈ₒq'
q⇒p (≈ₒ→≈ p≈ₒq) t = 
  let q' , t' , p'≈ₒq' = p≈ₒq .q⇒p t
  in q' , t' , ≈ₒ→≈ (≈ₒ-sym p'≈ₒq')
