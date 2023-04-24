open import Data.Bool
open import Data.Empty

import ccs.proc

module ccs.trans {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.proc {C} {N}

-- A transition between two CCS processes with through an action.
data Trans : Proc -> Act -> Proc -> Set₁ where
  chan    : forall {a p}
            -> Trans (chan a p) a p
  par-L   : forall {a pl pr p'}
            -> Trans pl a p'
            -> Trans (par pl pr) a (par p' pr)
  par-R   : forall {a pl pr p'}
            -> Trans pr a p' 
            -> Trans (par pl pr) a (par pl p')
  par-B   : forall {a pl pr pl' pr'}
            -> Trans pl a pl'
            -> Trans pr (flip-act a) pr'
            -> Trans (par pl pr) tau (par pl' pr')
  indet   : forall {S} {a q f}
            -> {s : S}
            -> Trans (f s) a q
            -> Trans (indet f) a q
  const   : forall {a p n}
            -> Trans (penv n) a p
            -> Trans (const n) a p
  rename  : forall {a p q r}
            -> Trans p a q
            -> Trans (rename r p) (map-action r a) (rename r q)
  hide    : forall {a p q f}
            -> {z : T (filter-act f a)}
            -> Trans p a q
            -> Trans (hide f p) a (hide f q)
