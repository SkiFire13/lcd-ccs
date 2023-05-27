{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.strong.relation (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.strong.base C N penv
open import bisimilarity.strong.correct-order C N penv

-- Definition of a strong bisimulation relation
record Bisimulation : Set₂ where
  field
    _R_ : Proc → Proc → Set₁
    p⇒q : ∀ {p a p' q} → p R q → (p -[ a ]→ p') → ∃[ q' ] (q -[ a ]→ q' × p' R q')
    q⇒p : ∀ {q a q' p} → p R q → (q -[ a ]→ q') → ∃[ p' ] (p -[ a ]→ p' × p' R q')
open Bisimulation renaming (_R_ to R)

-- Definition of strong bisimilarity as the biggest strong bisimulation
record _~ᵣ_ (p : Proc) (q : Proc) : Set₂ where
  constructor bisimilar
  field
    b : Bisimulation
    r : b .R p q
infixl 5 _~ᵣ_

-- Strong bisimilarity (defined with a relation) implies strong bisimilarity (coinductive with the correct order)
~ᵣ→~ₒ : ∀ {p q} → p ~ᵣ q → p ~ₒ q
p⇒q (~ᵣ→~ₒ (bisimilar R r)) t =
  let q' , t' , r' = R .p⇒q r t
  in  q' , t' , ~ᵣ→~ₒ (bisimilar R r')
q⇒p (~ᵣ→~ₒ (bisimilar R r)) t =
  let p' , t' , r' = R .q⇒p r t
  in  p' , t' , ~ᵣ→~ₒ (bisimilar R r')
  
-- Strong bisimilarity (coinductive with the correct order) implies strong bisimilarity (defined with a relation)
~ₒ→~ᵣ : ∀ {p q} → p ~ₒ q → p ~ᵣ q
~ₒ→~ᵣ p~ₒq = bisimilar bis p~ₒq
  where
  bis : Bisimulation
  R (bis) = _~ₒ_
  p⇒q (bis) p~q = _~ₒ_.p⇒q p~q
  q⇒p (bis) p~q = _~ₒ_.q⇒p p~q

-- Strong bisimilarity (defined with a relation) implies strong bisimilarity (coinductive)
~ᵣ→~ : ∀ {p q} → p ~ᵣ q → p ~ q
~ᵣ→~ p~ᵣq = ~ₒ→~ (~ᵣ→~ₒ p~ᵣq)

-- Strong bisimilarity (coinductive) implies strong bisimilarity (defined with a relation)
~→~ᵣ : ∀ {p q} → p ~ q → p ~ᵣ q
~→~ᵣ p~q = ~ₒ→~ᵣ (~→~ₒ p~q)
