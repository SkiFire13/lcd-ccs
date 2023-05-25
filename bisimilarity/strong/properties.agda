{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.strong.properties (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.strong.base C N penv

-- Properties of strong bisimilarity

reflexive : ∀ {p} → p ~ p
p⇒q (reflexive {p}) {p' = p'} t = p' , t , reflexive
q⇒p (reflexive {p}) {p' = p'} t = p' , t , reflexive

sym : ∀ {p q} → p ~ q → q ~ p
p⇒q (sym {p} {q} p~q) = p~q .q⇒p
q⇒p (sym {p} {q} p~q) = p~q .p⇒q

trans : ∀ {p q s} → p ~ q → q ~ s → p ~ s
p⇒q (trans {p} {q} {s} p~q q~s) tp =
  let q' , tq , p'~q' = p~q .p⇒q tp
      s' , ts , q'~s' = q~s .p⇒q tq
  in s' , ts , trans p'~q' q'~s'
q⇒p (trans {p} {q} {s} p~q q~s) = p⇒q (trans (sym q~s) (sym p~q))

-- Useful property
p~p+d : ∀ {p} → p ~ p + ccs.deadlock
p⇒q (p~p+d {p}) t = _ , indet t , reflexive
q⇒p (p~p+d {p}) (indet {s = right} (indet {s = ()} _))
q⇒p (p~p+d {p}) (indet {s = left} t) = _ , t , reflexive
