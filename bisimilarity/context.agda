import ccs.proc

module bisimilarity.context (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv hiding (deadlock)

-- A process context
data Context : Set₁ where
  chan    : Act → Context → Context
  par-L   : Context → Proc → Context
  par-R   : Proc → Context → Context
  indet   : Context → Proc → Context
  rename  : (C → C) → Context → Context
  hide    : (C → Set) → Context → Context
  replace : Context

-- Substitute a process inside a context
subst : Context → Proc → Proc
subst (chan a c) p = chan a (subst c p)
subst (par-L c q) p = par (subst c p) q
subst (par-R q c) p = par q (subst c p)
subst (indet c q) p = subst c p + q
subst (rename f c) p = rename f (subst c p)
subst (hide f c) p = hide f (subst c p)
subst replace p = p

-- Compose two processes in relation to subst
compose : Context → Context → Context
compose (chan a c) c2 = chan a (compose c c2)
compose (par-L c q) c2 = par-L (compose c c2) q
compose (par-R q c) c2 = par-R q (compose c c2)
compose (indet c q) c2 = indet (compose c c2) q
compose (rename f c) c2 = rename f (compose c c2)
compose (hide f c) c2 = hide f (compose c c2)
compose replace c2 = c2
