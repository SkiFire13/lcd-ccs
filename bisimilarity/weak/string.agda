{-# OPTIONS --safe --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.weak.string (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.weak.base C N penv

-- Weak string bisimilarity defined coinductively
record _≈ₛ_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p⇒q : ∀ {a p'} → (p =[ a ]⇒ p') → ∃[ q' ] (q =[ a ]⇒ q' × p' ≈ₛ q')
    q⇒p : ∀ {a q'} → (q =[ a ]⇒ q') → ∃[ p' ] (p =[ a ]⇒ p' × q' ≈ₛ p')
open _≈ₛ_ public
infixl 5 _≈ₛ_

-- Utilities to help prove ≈→≈ₛ
p⇒q-τ : ∀ {p q p'} → p ≈ q → (p -[τ]→* p') → ∃[ q' ] (q =[ τ ]⇒ q' × p' ≈ q')
p⇒q-τ p≈q self = _ , τ self , p≈q
p⇒q-τ p≈q (cons t s') =
  let q₁ , r₁ , p'≈q₁ = p≈q .p⇒q t
      q₂ , r₂ , p'≈q₂ = p⇒q-τ p'≈q₁ s'
  in  q₂ , join-t r₁ r₂ , p'≈q₂

p⇒q-split : ∀ {p₁ p₂ p₃ p₄ q a} → p₁ ≈ q → (p₁ -[τ]→* p₂) → (p₂ -[ a ]→ p₃) → (p₃ -[τ]→* p₄)
              → ∃[ q' ] (q =[ a ]⇒ q' × p₄ ≈ q')
p⇒q-split p≈q s₁ t s₂ =
  let q₁ , r₁ , p'≈q₁ = p⇒q-τ p≈q s₁
      q₂ , r₂ , p'≈q₂ = p'≈q₁ .p⇒q t
      q₃ , r₃ , p'≈q₃ = p⇒q-τ p'≈q₂ s₂
  in  q₃ , join-w r₁ r₂ r₃ , p'≈q₃

p⇒q-weak : ∀ {p q a p'} → p ≈ q → (p =[ a ]⇒ p') → ∃[ q' ] (q =[ a ]⇒ q' × p' ≈ q')
p⇒q-weak p≈q (send s₁ t s₂) = p⇒q-split p≈q s₁ t s₂
p⇒q-weak p≈q (recv s₁ t s₂) = p⇒q-split p≈q s₁ t s₂
p⇒q-weak p≈q (τ s)          = p⇒q-τ p≈q s

-- Weak string bisimilarity implies weak bisimilarity
≈ₛ→≈ : ∀ {p q} → p ≈ₛ q → p ≈ q
p⇒q (≈ₛ→≈ p≈ₛq) t =
  let q' , t' , p'≈ₛq' = p≈ₛq .p⇒q (trans→weak t)
  in  q' , t' , ≈ₛ→≈ p'≈ₛq'
q⇒p (≈ₛ→≈ p≈ₛq) t =
  let p' , t' , q'≈ₛp' = p≈ₛq .q⇒p (trans→weak t)
  in  p' , t' , ≈ₛ→≈ q'≈ₛp'

-- Weak bisimilarity implies weak string bisimilarity
≈→≈ₛ : ∀ {p q} → p ≈ q → p ≈ₛ q
q⇒p (≈→≈ₛ p≈q) = p⇒q (≈→≈ₛ record { p⇒q = p≈q .q⇒p ; q⇒p = p≈q .p⇒q })
p⇒q (≈→≈ₛ p≈q) t = let q' , t' , p'≈q' = p⇒q-weak p≈q t in q' , t' , ≈→≈ₛ p'≈q'
