open import Data.Bool
open import Data.Product

import ccs
import ccs.proc

module bisimilarity {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open ccs {C} {N} {penv}

BisimulationProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
BisimulationProperty R p q = (a : Act) -> (p' : Proc) -> Reduc p a p'
                             -> ∃[ q' ] (Reduc q a q' × R p' q')

subset-to-prop₂ : {A : Set₁} -> (A -> A -> Bool) -> (A -> A -> Set)
subset-to-prop₂ f = \ x y -> T (f x y)

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
