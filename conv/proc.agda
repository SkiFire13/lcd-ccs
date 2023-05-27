open import Base

module conv.proc (C N X V : Set) (Args : N → Set) where

-- The type of the channels (C) in the converted CCS
record Conv-C : Set where
  constructor conv-c
  field
    chan : C
    value : V

-- The type of the program names in the converted CCS
record Conv-N : Set where
  constructor conv-n
  field
    name : N
    args : Args name

open import ccs.proc Conv-C Conv-N as ccs
open import ccs-vp.proc C N X V Args as vp

conv-rename : (C → C) → (Conv-C → Conv-C)
conv-rename f = λ (conv-c c v) → conv-c (f c) v

conv-hide : Filter C → Filter Conv-C
conv-hide f = λ (conv-c c _) → f c

-- Convert a CCS VP process to a normal CCS Process
conv-proc : vp.Proc → ccs.Proc
conv-proc (send c v p)   = chan (send (conv-c c v)) (conv-proc p)
conv-proc (recv c f)     = indet (λ v → chan (recv (conv-c c v)) (conv-proc (f v)))
conv-proc (tau p)        = chan (tau) (conv-proc p)
conv-proc (par p q)      = par (conv-proc p) (conv-proc q)
conv-proc (indet f)      = indet (λ s → conv-proc (f s))
conv-proc (const n args) = const (conv-n n args)
conv-proc (rename f p)   = rename (conv-rename f) (conv-proc p)
conv-proc (hide f p)     = hide (conv-hide f) (conv-proc p)
conv-proc (if b p)       = if b then (conv-proc p) else ccs.deadlock

-- Convert a CCS VP action to a normal CCS action
conv-act : vp.Act → ccs.Act
conv-act (send c v) = send (conv-c c v)
conv-act (recv c v) = recv (conv-c c v)
conv-act tau        = tau

-- Convert a CCS VP process environment to a normal CCS process environment
conv-penv : vp.PEnv → ccs.PEnv
conv-penv penv (conv-n n env) = conv-proc (penv n env)
