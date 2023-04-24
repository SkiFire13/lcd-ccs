open import Data.Bool
open import Data.Unit

module conv.proc {C N X V : Set} {n-fv : N -> X -> Bool} where

-- The type of the channels (C) in the converted CCS
record Conv-C : Set where
  constructor conv-c
  field
    chan : C
    value : V

-- The type of the program constants (or, their names N) in the converted CCS
record Conv-N : Set where
  constructor conv-n
  field
    name : N
    args : (x : X) -> {_ : T (n-fv name x)} -> V

-- open import later to shadow `chan`
open import ccs.proc {Conv-C} {Conv-N} as ccs
open import ccs-vp.proc {C} {N} {X} {V} {n-fv} as vp

-- Convert a CCS-VP process to a normal CCS Process
-- the implementation is below, after a couple of helper co-recursive functions
conv-proc : vp.Proc -> ccs.Proc

conv-recv : C -> (V -> vp.Proc) -> V -> ccs.Proc
conv-recv c f = \ v -> chan (recv (conv-c c v)) (conv-proc (f v))

conv-indet : {S : Set} -> (S -> vp.Proc) -> S -> ccs.Proc
conv-indet f = \ s -> conv-proc (f s)

conv-rename : (C -> C) -> Conv-C -> Conv-C
conv-rename f = \ (conv-c c v) -> conv-c (f c) v

conv-hide : (C -> Bool) -> Conv-C -> Bool
conv-hide f = \ (conv-c c _) -> f c

conv-proc (chan-send c v p) = chan (send (conv-c c v)) (conv-proc p)
conv-proc (chan-recv c f)   = indet (conv-recv c f)
conv-proc (chan-tau p)      = chan (tau) (conv-proc p)
conv-proc (par p q)         = par (conv-proc p) (conv-proc q)
conv-proc (indet f)         = indet (conv-indet f)
conv-proc (const n args)    = const (conv-n n args)
conv-proc (rename f p)      = rename (conv-rename f) (conv-proc p)
conv-proc (hide f p)        = hide (conv-hide f) (conv-proc p)
conv-proc (if b p)          = if b then (conv-proc p) else ccs.deadlock

-- Convert reduction operations in CCS-VP into channel operations in CCS
conv-act : vp.Act -> ccs.Act
conv-act (send c v) = send (conv-c c v)
conv-act (recv c v) = recv (conv-c c v)
conv-act tau = tau

-- The converted process environment
conv-penv : vp.PEnv -> Conv-N -> ccs.Proc
conv-penv penv (conv-n n env) = conv-proc (penv n env)
