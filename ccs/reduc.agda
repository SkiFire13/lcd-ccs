open import Data.Bool
open import Data.Empty

import ccs.proc

module ccs.reduc {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open ccs.proc {C} {N}

-- A relation of reduction between two CCS processes with a channel operation.
data Reduc : Proc -> Act -> Proc -> Set₁ where
  chan    : forall {c p}
            -> Reduc (chan c p) c p
  par-L   : forall {c pl pr p'}
            -> Reduc pl c p'
            -> Reduc (par pl pr) c (par p' pr)
  par-R   : forall {c pl pr p'}
            -> Reduc pr c p' 
            -> Reduc (par pl pr) c (par pl p')
  par-B   : forall {c pl pr pl' pr'}
            -> Reduc pl c pl'
            -> Reduc pr (flip-act c) pr'
            -> Reduc (par pl pr) tau (par pl' pr')
  indet   : forall {S} {c q f}
            -> {s : S}
            -> Reduc (f s) c q
            -> Reduc (indet f) c q
  const   : forall {c p n}
            -> Reduc (penv n) c p
            -> Reduc (const n) c p
  rename  : forall {c p q r}
            -> Reduc p c q
            -> Reduc (rename r p) (map-action r c) (rename r q)
  hide    : forall {c p q f}
            -> {z : T (filter-act f c)}
            -> Reduc p c q
            -> Reduc (hide f p) c (hide f q)
 