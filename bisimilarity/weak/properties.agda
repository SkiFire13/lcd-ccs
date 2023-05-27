{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.weak.properties (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.strong.base C N penv
open import bisimilarity.strong.properties C N penv using () renaming (sym to ~-sym)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.string C N penv

-- Prove that ≈ is an equivalence

reflexive : ∀ {p} → p ≈ p
p⇒q (reflexive) t = _ , trans→weak t , reflexive
q⇒p (reflexive) t = _ , trans→weak t , reflexive

sym : ∀ {p q} → p ≈ q → q ≈ p
p⇒q (sym p≈q) = p≈q .q⇒p
q⇒p (sym p≈q) = p≈q .p⇒q

trans : ∀ {p q s} → p ≈ q → q ≈ s → p ≈ s
p⇒q (trans p≈q q≈s) tp =
  let q' , tq , p'≈q' = p≈q .p⇒q tp
      s' , ts , q'≈ₛs' = ≈→≈ₛ q≈s .p⇒q tq
  in  s' , ts , trans p'≈q' (≈ₛ→≈ q'≈ₛs')
q⇒p (trans p≈q q≈s) = p⇒q (trans (sym q≈s) (sym p≈q))

-- Conversion from strong to weak bisimilarity
~→≈ : ∀ {p q} → p ~ q → p ≈ q
p⇒q (~→≈ p~q) t =
  let q' , t' , p'~q' = p~q .p⇒q t
  in  q' , trans→weak t' , ~→≈ p'~q'
q⇒p (~→≈ p~q) = p⇒q (~→≈ (~-sym p~q))
