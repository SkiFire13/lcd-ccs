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
data _~ᵣ_ : Proc -> Proc -> Set₂ where
  bisimilar : (p : Proc) -> (q : Proc) -> (b : Bisimulation) -> b .R p q -> p ~ᵣ q

-- Strong bisimilarity (defined with a relation) implies strong bisimilarity (coinductive)
~ᵣ-to-~ : forall {p q} -> p ~ᵣ q -> p ~ q
p-to-q (~ᵣ-to-~ (bisimilar p q R x)) {p' = p'} t =
  let q' , t' , x' = R .p-to-q x t
  in q' , t' , ~ᵣ-to-~ (bisimilar p' q' R x')
q-to-p (~ᵣ-to-~ (bisimilar p q R x)) {p' = q'} t =
  let p' , t' , x' = R .q-to-p x t
  in p' , t' , ~ᵣ-to-~ (bisimilar q' p' R x')
-- Strong bisimilarity (coinductive) implies strong bisimilarity (defined with a relation)
~-to-~ᵣ : forall {p q} -> p ~ q -> p ~ᵣ q
~-to-~ᵣ {p} {q} p~q = bisimilar p q bis p~q
  where
  bis : Bisimulation
  R (bis) = _~_
  p-to-q (bis) = _~_.p-to-q
  q-to-p (bis) = _~_.q-to-p
