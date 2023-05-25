{-# OPTIONS --guardedness #-}

open import Data.Product

import ccs.proc

module bisimilarity.strong.relation (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.strong.base C N penv

-- Definition of a strong bisimulation
record Bisimulation : Set₂ where
  field
    R : Proc → Proc → Set₁
    p⇒q : ∀ {p q} → R p q → BisimulationProperty R p q
    q⇒p : ∀ {p q} → R p q → BisimulationProperty R q p
open Bisimulation

-- Definition of strong bisimilarity 
record _~ᵣ_ (p : Proc) (q : Proc) : Set₂ where
  constructor bisimilar
  field
    b : Bisimulation
    r : b .R p q

infixl 5 _~ᵣ_

~ᵣ→~ : ∀ {p q} → p ~ᵣ q → p ~ q
p⇒q (~ᵣ→~ (bisimilar R r)) t =
  let q' , t' , r' = R .p⇒q r t
  in q' , t' , ~ᵣ→~ (bisimilar R r')
q⇒p (~ᵣ→~ (bisimilar R r)) t =
  let p' , t' , r' = R .q⇒p r t
  in p' , t' , ~ᵣ→~ (bisimilar R r')
~→~ᵣ : ∀ {p q} → p ~ q → p ~ᵣ q
~→~ᵣ {p} {q} p~q = bisimilar bis p~q
  where
  bis : Bisimulation
  R (bis) = _~_
  p⇒q (bis) = _~_.p⇒q
  q⇒p (bis) = _~_.q⇒p
