open import Data.Bool
open import Data.Empty

import ccs-vp.proc

module ccs-vp.trans {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open import ccs-vp.proc {C} {N} {X} {V} {n-fv}

-- A transition between two CCS VP processes through an action.
data Trans : Proc -> Act -> Proc -> Set₁ where
  send   : forall {a v p}
           -> Trans (send a v p) (send a v) p
  recv   : forall {a v f}
           -> Trans (recv a f) (recv a v) (f v)
  tau    : forall {p}
           -> Trans (tau p) tau p
  par-L  : forall {a pl pr p'}
           -> Trans pl a p'
           -> Trans (par pl pr) a (par p' pr)
  par-R  : forall {a pl pr p'}
           -> Trans pr a p'
           -> Trans (par pl pr) a (par pl p')
  par-B  : forall {a pl pr pl' pr'}
           -> Trans pl a pl'
           -> Trans pr (flip-act a) pr'
           -> Trans (par pl pr) tau (par pl' pr')
  indet  : forall {a q S f} {s : S}
           -> Trans (f s) a q
           -> Trans (indet f) a q
  const  : forall {a p n f}
           -> Trans (penv n f) a p
           -> Trans (const n f) a p
  rename : forall {a p q r}
           -> Trans p a q
           -> Trans (rename r p) (map-act r a) (rename r q)
  hide   : forall {a p q f} {z : T (filter-act f a)}
           -> Trans p a q
           -> Trans (hide f p) a (hide f q)
  if     : forall {a p q}
           -> Trans p a q
           -> Trans (if true p) a q
