{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product

import ccs.proc

module bisimilarity.strong.properties (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.strong.base C N penv

-- Properties of strong bisimilarity

reflexive : ∀ {p} → p ~ p
p-to-q (reflexive {p}) {p' = p'} t = p' , t , reflexive
q-to-p (reflexive {p}) {p' = p'} t = p' , t , reflexive

sym : ∀ {p q} → p ~ q → q ~ p
p-to-q (sym {p} {q} p~q) = p~q .q-to-p
q-to-p (sym {p} {q} p~q) = p~q .p-to-q

trans : ∀ {p q s} → p ~ q → q ~ s → p ~ s
p-to-q (trans {p} {q} {s} p~q q~s) tp =
  let q' , tq , p'~q' = p~q .p-to-q tp
      s' , ts , q'~s' = q~s .p-to-q tq
  in s' , ts , trans p'~q' q'~s'
q-to-p (trans {p} {q} {s} p~q q~s) = p-to-q (trans (sym q~s) (sym p~q))

-- Useful property
p~p+d : ∀ {p} → p ~ p + ccs.deadlock
p-to-q (p~p+d {p}) t = _ , indet t , reflexive
q-to-p (p~p+d {p}) (indet {s = false} (indet {s = ()} _))
q-to-p (p~p+d {p}) (indet {s = true} t) = _ , t , reflexive
