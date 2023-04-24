open import Data.Bool
open import Data.Empty

import ccs.proc

module ccs.reduc {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.proc {C} {N}

-- A relation of reduction between two CCS processes with a channel operation.
data Reduc : Proc -> Act -> Proc -> Set₁ where
  chan    : forall {a p}
            -> Reduc (chan a p) a p
  par-L   : forall {a pl pr p'}
            -> Reduc pl a p'
            -> Reduc (par pl pr) a (par p' pr)
  par-R   : forall {a pl pr p'}
            -> Reduc pr a p' 
            -> Reduc (par pl pr) a (par pl p')
  par-B   : forall {a pl pr pl' pr'}
            -> Reduc pl a pl'
            -> Reduc pr (flip-act a) pr'
            -> Reduc (par pl pr) tau (par pl' pr')
  indet   : forall {S} {a q f}
            -> {s : S}
            -> Reduc (f s) a q
            -> Reduc (indet f) a q
  const   : forall {a p n}
            -> Reduc (penv n) a p
            -> Reduc (const n) a p
  rename  : forall {a p q r}
            -> Reduc p a q
            -> Reduc (rename r p) (map-action r a) (rename r q)
  hide    : forall {a p q f}
            -> {z : T (filter-act f a)}
            -> Reduc p a q
            -> Reduc (hide f p) a (hide f q)
 