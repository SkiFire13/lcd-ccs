{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product

import ccs.proc

module bisimilarity.weak.properties (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.strong.base C N penv
open import bisimilarity.strong.properties C N penv using () renaming (sym to ~-sym)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.string C N penv

-- Properties of weak bisimilarity

reflexive : ∀ {p} → p ≈ p
p-to-q (reflexive {p}) {p' = p'} t = p' , trans-to-weak t , reflexive
q-to-p (reflexive {p}) {p' = p'} t = p' , trans-to-weak t , reflexive

sym : ∀ {p q} → p ≈ q → q ≈ p
p-to-q (sym {p} {q} p≈q) = p≈q .q-to-p
q-to-p (sym {p} {q} p≈q) = p≈q .p-to-q

trans : ∀ {p q s} → p ≈ q → q ≈ s → p ≈ s
p-to-q (trans {p} {q} {s} p≈q q≈s) tp =
  let q' , tq , p'≈q' = p≈q .p-to-q tp
      s' , ts , q'≈ₛs' = ≈-to-≈ₛ q≈s .p-to-q tq
      q'≈s' = ≈ₛ-to-≈ q'≈ₛs'
  in s' , ts , trans p'≈q' q'≈s'
q-to-p (trans {p} {q} {s} p≈q q≈s) = p-to-q (trans (sym q≈s) (sym p≈q))

-- Conversion from strong to weak bisimilarity
~-to-≈ : ∀ {p q} → p ~ q → p ≈ q
p-to-q (~-to-≈ p~q) t =
  let q' , t' , p'~q' = p~q .p-to-q t
  in q' , trans-to-weak t' , ~-to-≈ p'~q'
q-to-p (~-to-≈ p~q) = p-to-q (~-to-≈ (~-sym p~q))

-- Useful property
p≈p+d : ∀ {p} → p ≈ indet₂ p ccs.deadlock
p-to-q (p≈p+d) {p' = p'} t = p' , trans-to-weak (indet t) , reflexive
q-to-p (p≈p+d) (indet {q = p'} {s = true} t) = p' , trans-to-weak t , reflexive
q-to-p (p≈p+d) (indet {s = false} (indet {s = ()} _))
