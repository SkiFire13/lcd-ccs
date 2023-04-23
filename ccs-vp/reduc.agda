open import Data.Bool
open import Data.Empty

import ccs-vp.proc

module ccs-vp.reduc {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open ccs-vp.proc {C} {N} {X} {V} {n-fv}

-- A relation of reduction between two CCS-VP processes with a reduction operation.
data Reduc : Proc -> Act -> Proc -> Set₁ where
  chan-send : forall {a v p}
              -> Reduc (chan-send a v p) (send a v) p
  chan-recv : forall {a v f}
              -> Reduc (chan-recv a f) (recv a v) (f v)
  chan-tau  : forall {p}
              -> Reduc (chan-tau p) tau p
  par-L     : forall {a pl pr p'}
              -> Reduc pl a p'
              -> Reduc (par pl pr) a (par p' pr)
  par-R     : forall {a pl pr p'}
              -> Reduc pr a p'
              -> Reduc (par pl pr) a (par pl p')
  par-B     : forall {a pl pr pl' pr'}
              -> Reduc pl a pl'
              -> Reduc pr (flip-act a) pr'
              -> Reduc (par pl pr) tau (par pl' pr')
  indet     : forall {a q S f}
              -> {s : S}
              -> Reduc (f s) a q
              -> Reduc (indet f) a q
  const     : forall {a p n f}
              -> Reduc (penv n f) a p
              -> Reduc (const n f) a p
  rename    : forall {a p q r}
              -> Reduc p a q
              -> Reduc (rename r p) (map-act r a) (rename r q)
  hide      : forall {a p q f}
              -> {z : T (filter-act f a)}
              -> Reduc p a q
              -> Reduc (hide f p) a (hide f q)
  if        : forall {a p q}
              -> Reduc p a q
              -> Reduc (if true p) a q
