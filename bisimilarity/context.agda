open import Data.Bool
open import Data.Empty

import ccs.proc

module bisimilarity.context {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} hiding (deadlock)

-- A process context
-- TODO: force one and only one replacement
-- TODO: decide what to do with `indet`
data Context : Set₁ where
  chan    : Act -> Context -> Context
  par     : Context -> Context -> Context
  indet   : {S : Set} -> (S -> Context) -> Context
  const   : N -> Context
  rename  : (C -> C) -> Context -> Context
  hide    : (C -> Bool) -> Context -> Context
  replace : Context

-- Substitute a process inside a context
subst : Context -> Proc -> Proc
subst (chan a c) p = chan a (subst c p)
subst (par cl cr) p = par (subst cl p) (subst cr p)
subst (indet f) p = indet (\ s -> subst (f s) p)
subst (const n) p = const n
subst (rename f c) p = rename f (subst c p)
subst (hide f c) p = hide f (subst c p)
subst replace p = p

deadlock : Context
deadlock = indet ⊥-elim

compose : Context -> Context -> Context
compose (chan a c) c2 = chan a (compose c c2)
compose (par cl cr) c2 = par (compose cl c2) (compose cr c2)
compose (indet f) c2 = indet (\ s -> compose (f s) c2)
compose (const n) c2 = const n
compose (rename f c) c2 = rename f (compose c c2)
compose (hide f c) c2 = hide f (compose c c2)
compose replace c2 = c2
