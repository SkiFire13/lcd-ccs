open import Data.Bool
open import Data.Empty

import ccs-vp.proc

module ccs-vp.trans (C N X V : Set) (n-fv : N → X → Bool) (penv : ccs-vp.proc.PEnv C N X V n-fv) where

open import ccs-vp.proc C N X V n-fv

private
  variable
    {p q p'} : Proc
    {pl pr pl' pr'} : Proc
    {a} : Act
    {c} : C
    {n} : N
    {v} : V

-- A transition between two CCS VP processes through an action.
data Trans : Proc → Act → Proc → Set₁ where
  send   : Trans (send c v p) (send c v) p
  recv   : ∀ {f} → Trans (recv c f) (recv c v) (f v)
  tau    : Trans (tau p) tau p
  par-L  : Trans pl a p' → Trans (par pl pr) a (par p' pr)
  par-R  : Trans pr a p' → Trans (par pl pr) a (par pl p')
  par-B  : Trans pl a pl' → Trans pr (flip-act a) pr' → Trans (par pl pr) tau (par pl' pr')
  indet  : ∀ {S f} {s : S} → Trans (f s) a q → Trans (indet f) a q
  const  : ∀ {f} → Trans (penv n f) a p → Trans (const n f) a p
  rename : ∀ {f} → Trans p a q → Trans (rename f p) (map-act f a) (rename f q)
  hide   : ∀ {f} {z : T (filter-act f a)} → Trans p a q → Trans (hide f p) a (hide f q)
  if     : Trans p a q → Trans (if true p) a q
