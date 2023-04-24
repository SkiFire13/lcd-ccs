open import Data.Bool
open import Data.Product
open import Relation.Binary.Definitions

import ccs
import ccs.proc

module bisimilarity {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open ccs {C} {N} {penv}

BisimulationProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
BisimulationProperty R p q = (a : Act) -> (p' : Proc) -> Reduc p a p'
                             -> ∃[ q' ] (Reduc q a q' × R p' q')

record Bisimulation : Set₂ where
  field
    R : Proc -> Proc -> Set₁
    p-to-q : forall {p q} -> R p q -> BisimulationProperty R p q
    q-to-p : forall {p q} -> R p q -> BisimulationProperty R q p
open Bisimulation

data _∼_ : Proc -> Proc -> Set₂ where
  bisimilar : (p : Proc) -> (q : Proc) -> (b : Bisimulation) -> b .R p q -> p ∼ q

record _~_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : BisimulationProperty _~_ p q
    q-to-p : BisimulationProperty _~_ q p
open _~_

∼-to-~ : forall {p q} -> p ∼ q -> p ~ q
p-to-q (∼-to-~ (bisimilar p q R x)) a p' r =
  let q' , r' , x' = R .p-to-q {p} {q} x a p' r
  in q' , r' , ∼-to-~ (bisimilar p' q' R x')
q-to-p (∼-to-~ (bisimilar p q R x)) a q' r =
  let p' , r' , x' = R .q-to-p {p} {q} x a q' r
  in p' , r' , ∼-to-~ (bisimilar q' p' R x')

~-to-∼ : forall {p q} -> p ~ q -> p ∼ q
~-to-∼ {p} {q} p~q = bisimilar p q bis p~q
  where
  bis : Bisimulation
  R (bis) = _~_
  p-to-q (bis) = p-to-q
  q-to-p (bis) = q-to-p

~-Reflexive : Reflexive _~_
p-to-q (~-Reflexive {p}) _ p' r = p' , r , ~-Reflexive
q-to-p (~-Reflexive {p}) _ p' r = p' , r , ~-Reflexive

~-Symmetric : Symmetric _~_
p-to-q (~-Symmetric {p} {q} p~q) = p~q .q-to-p
q-to-p (~-Symmetric {p} {q} p~q) = p~q .p-to-q

~-Transitive : Transitive _~_
p-to-q (~-Transitive {p} {q} {s} p~q q~s) a p' rp =
  let q' , rq , p'~q' = p~q .p-to-q a p' rp
      s' , rs , q'~s' = q~s .p-to-q a q' rq
  in s' , rs , ~-Transitive p'~q' q'~s'
q-to-p (~-Transitive {p} {q} {s} p~q q~s) a s' rp =
  let q' , rq , s'~q' = q~s .q-to-p a s' rp
      p' , rp , q'~p' = p~q .q-to-p a q' rq
  in p' , rp , ~-Transitive s'~q' q'~p'
