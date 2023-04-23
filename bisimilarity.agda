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
    subset : Proc -> Proc -> Set₁
    p-to-q : forall {p q} -> subset p q -> BisimulationProperty subset p q
    q-to-p : forall {p q} -> subset p q -> BisimulationProperty subset q p
open Bisimulation

data _∼_ : Proc -> Proc -> Set₂ where
  bisimilar : (p : Proc)
              -> (q : Proc)
              -> (R : Bisimulation)
              -> R .subset p q
              -> p ∼ q

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
~-to-∼ {p} {q} r = let
    bisimulation = record {
        subset = _~_ ;
        p-to-q = p-to-q ;
        q-to-p = q-to-p
      }
  in bisimilar p q bisimulation r

~-Reflexive : Reflexive _~_
p-to-q (~-Reflexive {p}) _ p' r = p' , r , ~-Reflexive
q-to-p (~-Reflexive {p}) _ p' r = p' , r , ~-Reflexive

~-Symmetric : Symmetric _~_
p-to-q (~-Symmetric {p} {q} r) = r .q-to-p
q-to-p (~-Symmetric {p} {q} r) = r .p-to-q

~-Transitive : Transitive _~_
p-to-q (~-Transitive {p} {q} {s} r1 r2) a p' rp =
  let q' , rq , r' = r1 .p-to-q a p' rp
      s' , rs , r'' = r2 .p-to-q a q' rq
  in s' , rs , ~-Transitive r' r''
q-to-p (~-Transitive {p} {q} {s} r1 r2) a s' r =
  let q' , rq , r' = r2 .q-to-p a s' r
      p' , rp , r'' = r1 .q-to-p a q' rq
  in p' , rp , ~-Transitive r' r''
