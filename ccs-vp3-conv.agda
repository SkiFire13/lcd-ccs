open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable

import ccs
import ccs-vp3 as ccs-vp

module ccs-vp3-conv
  {C N X V : Set}
  {n-fv : N -> X -> Bool}
  {n-to-prog : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> ccs-vp.Prog {C} {N} {X} {V} {n-fv}}
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
conv (ccs-vp.hide f p) = ccs.hide (\ (conv-c c v) -> f c) (conv p)
conv (ccs-vp.if b p) = ccs.indet (\ s -> if isYes (s ≟ b) then conv p else ccs.deadlock)
