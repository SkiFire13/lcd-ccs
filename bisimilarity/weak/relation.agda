{-# OPTIONS --safe --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.weak.relation (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.correct-order C N penv

-- Definition of a weak bisimulation relation
record Bisimulation : Set₂ where
  field
    _R_ : Proc → Proc → Set₁
    p⇒q : ∀ {p a p' q} → p R q → (p -[ a ]→ p') → ∃[ q' ] (q =[ a ]⇒ q' × p' R q')
    q⇒p : ∀ {q a q' p} → p R q → (q -[ a ]→ q') → ∃[ p' ] (p =[ a ]⇒ p' × p' R q')
open Bisimulation renaming (_R_ to R)

-- Definition of weak bisimilarity as the biggest weak bisimulation
record _≈ᵣ_ (p : Proc) (q : Proc) : Set₂ where
  constructor bisimilar
  field
    b : Bisimulation
    w : b .R p q
infixl 5 _≈ᵣ_

-- Weak bisimilarity (defined with a relation) implies weak bisimilarity (coinductive with the correct order)
≈ᵣ→≈ₒ : ∀ {p q} → p ≈ᵣ q → p ≈ₒ q
p⇒q (≈ᵣ→≈ₒ (bisimilar B w)) t =
  let q' , t' , w' = B .p⇒q w t
  in  q' , t' , ≈ᵣ→≈ₒ (bisimilar B w')
q⇒p (≈ᵣ→≈ₒ (bisimilar B w)) t =
  let p' , t' , w' = B .q⇒p w t
  in  p' , t' , ≈ᵣ→≈ₒ (bisimilar B w')

-- Weak bisimilarity (coinductive with the correct order) implies weak bisimilarity (defined with a relation)
≈ₒ→≈ᵣ : ∀ {p q} → p ≈ₒ q → p ≈ᵣ q
≈ₒ→≈ᵣ {p} {q} p≈ₒq = bisimilar bis p≈ₒq
  where
  bis : Bisimulation
  R (bis) = _≈ₒ_
  p⇒q (bis) p≈ₒq = _≈ₒ_.p⇒q p≈ₒq
  q⇒p (bis) p≈ₒq = _≈ₒ_.q⇒p p≈ₒq

-- Weak bisimilarity (defined with a relation) implies weak bisimilarity (coinductive)
≈ᵣ→≈ : ∀ {p q} → p ≈ᵣ q → p ≈ q
≈ᵣ→≈ p≈ᵣq = ≈ₒ→≈ (≈ᵣ→≈ₒ p≈ᵣq)

-- Weak bisimilarity (coinductive) implies weak bisimilarity (defined with a relation)
≈→≈ᵣ : ∀ {p q} → p ≈ q → p ≈ᵣ q
≈→≈ᵣ p≈q = ≈ₒ→≈ᵣ (≈→≈ₒ p≈q)
