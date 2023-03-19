open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

import ccs
import ccs-vp3 as ccs-vp

module ccs-vp3-conv
  {C N X V : Set}
  {n-fv : N -> X -> Bool}
  {penv : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> ccs-vp.Prog {C} {N} {X} {V} {n-fv}}
  where

record Conv-C : Set where
  constructor conv-c
  field
    chan : C
    value : V

record Conv-N : Set where
  constructor conv-n
  field
    name : N
    args : (x : X) -> {_ : T (n-fv name x)} -> V

conv : ccs-vp.Prog -> ccs.Prog
conv (ccs-vp.chan-send c v p) = ccs.chan (ccs.send (conv-c c v)) (conv p)
conv (ccs-vp.chan-recv c f) = ccs.indet {S = V} (\ v -> ccs.chan (ccs.recv (conv-c c v)) (conv (f v)))
conv (ccs-vp.chan-tau p) = ccs.chan (ccs.tau) (conv p)
conv (ccs-vp.par p q) = ccs.par (conv p) (conv q)
conv (ccs-vp.indet f) = ccs.indet \ s -> conv (f s)
conv (ccs-vp.const n args) = ccs.const (conv-n n args)
conv (ccs-vp.rename f p) = ccs.rename (\ (conv-c c v) -> conv-c (f c) v) (conv p)
conv (ccs-vp.hide f p) = ccs.hide (\ (conv-c c _) -> f c) (conv p)
conv (ccs-vp.if b p) = ccs.indet (\ s -> if isYes (s ≟ b) then conv p else ccs.deadlock)

conv-red : ccs-vp.ReducOp {C} {N} {X} {V} {n-fv} -> ccs.ChanOp {Conv-C} {Conv-N}
conv-red (ccs-vp.send c v) = ccs.send (conv-c c v)
conv-red (ccs-vp.recv c v) = ccs.recv (conv-c c v)
conv-red ccs-vp.tau = ccs.tau

conv-eqv : forall {p1 c p2} -> ccs-vp.Reduces p1 c p2 -> ccs.Reduces (conv p1) (conv-red c) (conv p2)
conv-eqv ccs-vp.chan-send = ccs.chan
conv-eqv ccs-vp.chan-recv = ccs.indet ccs.chan
conv-eqv ccs-vp.chan-tau = ccs.chan
conv-eqv (ccs-vp.par-L r) = ccs.par-L (conv-eqv r)
conv-eqv (ccs-vp.par-R r) = ccs.par-R (conv-eqv r)
conv-eqv (ccs-vp.par-B {c} rl rr) with c
... | ccs-vp.send _ _ = ccs.par-B (conv-eqv rl) (conv-eqv rr)
... | ccs-vp.recv _ _ = ccs.par-B (conv-eqv rl) (conv-eqv rr)
... | ccs-vp.tau      = ccs.par-B (conv-eqv rl) (conv-eqv rr)
conv-eqv (ccs-vp.indet r) = ccs.indet (conv-eqv r)
conv-eqv (ccs-vp.const {penv = penv} r) = ccs.const {penv = \ (conv-n n env) -> conv (penv n env)} (conv-eqv r)
conv-eqv (ccs-vp.rename {c} r) with c
... | ccs-vp.send _ _ = ccs.rename (conv-eqv r)
... | ccs-vp.recv _ _ = ccs.rename (conv-eqv r)
... | ccs-vp.tau      = ccs.rename (conv-eqv r)
conv-eqv (ccs-vp.hide {c = c} {f = f} {z = z} r) with c
... | ccs-vp.send _ _ = ccs.hide {z = z} (conv-eqv r)
... | ccs-vp.recv _ _ = ccs.hide {z = z} (conv-eqv r)
... | ccs-vp.tau      = ccs.hide {z = z} (conv-eqv r)
conv-eqv (ccs-vp.if r) = ccs.indet {s = true} (conv-eqv r)
