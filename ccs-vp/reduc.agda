open import Data.Bool
open import Data.Empty

import ccs-vp.proc

module ccs-vp.reduc {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open ccs-vp.proc {C} {N} {X} {V} {n-fv}

-- A relation of reduction between two CCS-VP processes with a reduction operation.
data Reduc : Proc -> Act -> Proc -> Set₁ where
  chan-send : forall {c v p}
              -> Reduc (chan-send c v p) (send c v) p
  chan-recv : forall {c v f}
              -> Reduc (chan-recv c f) (recv c v) (f v)
  chan-tau  : forall {p}
              -> Reduc (chan-tau p) tau p
  par-L     : forall {c pl pr p'}
              -> Reduc pl c p'
              -> Reduc (par pl pr) c (par p' pr)
  par-R     : forall {c pl pr p'}
              -> Reduc pr c p'
              -> Reduc (par pl pr) c (par pl p')
  par-B     : forall {c pl pr pl' pr'}
              -> Reduc pl c pl'
              -> Reduc pr (flip-act c) pr'
              -> Reduc (par pl pr) tau (par pl' pr')
  indet     : forall {c q S f}
              -> {s : S}
              -> Reduc (f s) c q
              -> Reduc (indet f) c q
  const     : forall {c p n f}
              -> Reduc (penv n f) c p
              -> Reduc (const n f) c p
  rename    : forall {c p q r}
              -> Reduc p c q
              -> Reduc (rename r p) (map-act r c) (rename r q)
  hide      : forall {c p q f}
              -> {z : T (filter-act f c)}
              -> Reduc p c q
              -> Reduc (hide f p) c (hide f q)
  if        : forall {c p q}
              -> Reduc p c q
              -> Reduc (if true p) c q
