open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

module ccs-vp3-conv
  {C N X V : Set}
  {n-fv : N -> X -> Bool}
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

import ccs as ccs-real
import ccs-vp3 as ccs-vp-real
module ccs = ccs-real {Conv-C} {Conv-N}
module ccs-vp = ccs-vp-real {C} {N} {X} {V} {n-fv}

variable
  penv : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> ccs-vp.Prog

conv-prog : ccs-vp.Prog -> ccs.Prog
conv-prog (ccs-vp.chan-send c v p) = ccs.chan (ccs.send (conv-c c v)) (conv-prog p)
conv-prog (ccs-vp.chan-recv c f) = ccs.indet {S = V} (\ v -> ccs.chan (ccs.recv (conv-c c v)) (conv-prog (f v)))
conv-prog (ccs-vp.chan-tau p) = ccs.chan (ccs.tau) (conv-prog p)
conv-prog (ccs-vp.par p q) = ccs.par (conv-prog p) (conv-prog q)
conv-prog (ccs-vp.indet f) = ccs.indet \ s -> conv-prog (f s)
conv-prog (ccs-vp.const n args) = ccs.const (conv-n n args)
conv-prog (ccs-vp.rename f p) = ccs.rename (\ (conv-c c v) -> conv-c (f c) v) (conv-prog p)
conv-prog (ccs-vp.hide f p) = ccs.hide (\ (conv-c c _) -> f c) (conv-prog p)
conv-prog (ccs-vp.if b p) = ccs.indet (\ s -> if isYes (s ≟ b) then conv-prog p else ccs.deadlock)

conv-reduc-op : ccs-vp.ReducOp -> ccs.ChanOp
conv-reduc-op (ccs-vp.send c v) = ccs.send (conv-c c v)
conv-reduc-op (ccs-vp.recv c v) = ccs.recv (conv-c c v)
conv-reduc-op ccs-vp.tau = ccs.tau

conv-reduces : forall {p1 c p2} -> ccs-vp.Reduces p1 c p2 -> ccs.Reduces (conv-prog p1) (conv-reduc-op c) (conv-prog p2)
conv-reduces ccs-vp.chan-send = ccs.chan
conv-reduces ccs-vp.chan-recv = ccs.indet ccs.chan
conv-reduces ccs-vp.chan-tau = ccs.chan
conv-reduces (ccs-vp.par-L r) = ccs.par-L (conv-reduces r)
conv-reduces (ccs-vp.par-R r) = ccs.par-R (conv-reduces r)
conv-reduces (ccs-vp.par-B {c} rl rr) with c
... | ccs-vp.send _ _ = ccs.par-B (conv-reduces rl) (conv-reduces rr)
... | ccs-vp.recv _ _ = ccs.par-B (conv-reduces rl) (conv-reduces rr)
... | ccs-vp.tau      = ccs.par-B (conv-reduces rl) (conv-reduces rr)
conv-reduces (ccs-vp.indet r) = ccs.indet (conv-reduces r)
conv-reduces (ccs-vp.const {penv = penv} r) = ccs.const {penv = \ (conv-n n env) -> conv-prog (penv n env)} (conv-reduces r)
conv-reduces (ccs-vp.rename {c} r) with c
... | ccs-vp.send _ _ = ccs.rename (conv-reduces r)
... | ccs-vp.recv _ _ = ccs.rename (conv-reduces r)
... | ccs-vp.tau      = ccs.rename (conv-reduces r)
conv-reduces (ccs-vp.hide {c} {z = z} r) with c
... | ccs-vp.send _ _ = ccs.hide {z = z} (conv-reduces r)
... | ccs-vp.recv _ _ = ccs.hide {z = z} (conv-reduces r)
... | ccs-vp.tau      = ccs.hide {z = z} (conv-reduces r)
conv-reduces (ccs-vp.if r) = ccs.indet {s = true} (conv-reduces r)
