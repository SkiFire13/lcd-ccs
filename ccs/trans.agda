open import Data.Bool
open import Data.Empty

import ccs.proc

module ccs.trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.proc C N

private
  variable
    {p q p'} : Proc
    {pl pr pl' pr'} : Proc
    {a} : Act
    {n} : N

-- A transition between two CCS processes with through an action.
data Trans : Proc → Act → Proc → Set₁ where
  chan    : Trans (chan a p) a p
  par-L   : Trans pl a p' → Trans (par pl pr) a (par p' pr)
  par-R   : Trans pr a p' → Trans (par pl pr) a (par pl p')
  par-B   : Trans pl a pl' → Trans pr (flip-act a) pr' → Trans (par pl pr) tau (par pl' pr')
  indet   : ∀ {S f} {s : S} → Trans (f s) a q → Trans (indet f) a q
  const   : Trans (penv n) a p → Trans (const n) a p
  rename  : ∀ {f} → Trans p a q → Trans (rename f p) (map-act f a) (rename f q)
  hide    : ∀ {f} {z : T (filter-act f a)} → Trans p a q → Trans (hide f p) a (hide f q)
