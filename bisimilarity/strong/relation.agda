{-# OPTIONS --guardedness #-}

open import Data.Product

import ccs.proc

module bisimilarity.strong.relation {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.strong.base {C} {N} {penv}

-- Definition of a strong bisimulation
record Bisimulation : Set₂ where
  field
    R : Proc -> Proc -> Set₁
    p-to-q : forall {p q} -> R p q -> BisimulationProperty R p q
    q-to-p : forall {p q} -> R p q -> BisimulationProperty R q p
open Bisimulation

-- Definition of strong bisimilarity 
record _~ᵣ_ (p : Proc) (q : Proc) : Set₂ where
  constructor bisimilar
  field
    b : Bisimulation
    r : b .R p q

~ᵣ-to-~ : forall {p q} -> p ~ᵣ q -> p ~ q
p-to-q (~ᵣ-to-~ (bisimilar R r)) t =
  let q' , t' , r' = R .p-to-q r t
  in q' , t' , ~ᵣ-to-~ (bisimilar R r')
q-to-p (~ᵣ-to-~ (bisimilar R r)) t =
  let p' , t' , r' = R .q-to-p r t
  in p' , t' , ~ᵣ-to-~ (bisimilar R r')
~-to-~ᵣ : forall {p q} -> p ~ q -> p ~ᵣ q
~-to-~ᵣ {p} {q} p~q = bisimilar bis p~q
  where
  bis : Bisimulation
  R (bis) = _~_
  p-to-q (bis) = _~_.p-to-q
  q-to-p (bis) = _~_.q-to-p
