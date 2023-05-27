{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.strong.properties (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.strong.base C N penv

-- Prove that ~ is an equivalence

reflexive : ∀ {p} → p ~ p
p⇒q (reflexive) t = _ , t , reflexive
q⇒p (reflexive) t = _ , t , reflexive

sym : ∀ {p q} → p ~ q → q ~ p
p⇒q (sym p~q) = p~q .q⇒p
q⇒p (sym p~q) = p~q .p⇒q

trans : ∀ {p q s} → p ~ q → q ~ s → p ~ s
p⇒q (trans p~q q~s) tp =
  let q' , tq , p'~q' = p~q .p⇒q tp
      s' , ts , q'~s' = q~s .p⇒q tq
  in  s' , ts , trans p'~q' q'~s'
q⇒p (trans p~q q~s) = p⇒q (trans (sym q~s) (sym p~q))
