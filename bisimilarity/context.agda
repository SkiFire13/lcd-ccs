open import Data.Bool

import ccs.proc

module bisimilarity.context {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs {C} {N} {penv}

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
subst (par c1 c2) p = par (subst c1 p) (subst c2 p)
subst (indet f) p = indet (\ s -> subst (f s) p)
subst (const n) p = const n
subst (rename f c) p = rename f (subst c p)
subst (hide f c) p = hide f (subst c p)
subst replace p = p