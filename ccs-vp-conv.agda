open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit

import ccs as ccs-real
import ccs-vp as ccs-vp-real

module ccs-vp-conv
  {C N X V : Set}
  {n-fv : N -> X -> Bool}
  {penv : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> ccs-vp-real.Prog {C} {N} {X} {V} {n-fv}}
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

module ccs = ccs-real {Conv-C} {Conv-N}
module ccs-vp = ccs-vp-real {C} {N} {X} {V} {n-fv}

conv-rename : (C -> C) -> Conv-C -> Conv-C
conv-rename f (conv-c c v) = conv-c (f c) v

conv-hide : (C -> Bool) -> Conv-C -> Bool
conv-hide f (conv-c c _) = f c

conv-prog : ccs-vp.Prog -> ccs.Prog
conv-prog (ccs-vp.chan-send c v p) = ccs.chan (ccs.send (conv-c c v)) (conv-prog p)
conv-prog (ccs-vp.chan-recv c f) = ccs.indet {S = V} (\ v -> ccs.chan (ccs.recv (conv-c c v)) (conv-prog (f v)))
conv-prog (ccs-vp.chan-tau p) = ccs.chan (ccs.tau) (conv-prog p)
conv-prog (ccs-vp.par p q) = ccs.par (conv-prog p) (conv-prog q)
conv-prog (ccs-vp.indet f) = ccs.indet \ s -> conv-prog (f s)
conv-prog (ccs-vp.const n args) = ccs.const (conv-n n args)
conv-prog (ccs-vp.rename f p) = ccs.rename (conv-rename f) (conv-prog p)
conv-prog (ccs-vp.hide f p) = ccs.hide (conv-hide f) (conv-prog p)
conv-prog (ccs-vp.if b p) = ccs.indet {S = if b then ⊤ else ⊥} (\ _ -> conv-prog p)

conv-penv : ((conv-n n env) : Conv-N) -> ccs.Prog
conv-penv (conv-n n env) = conv-prog (penv n env)

conv-reduc-op : ccs-vp.ReducOp -> ccs.ChanOp
conv-reduc-op (ccs-vp.send c v) = ccs.send (conv-c c v)
conv-reduc-op (ccs-vp.recv c v) = ccs.recv (conv-c c v)
conv-reduc-op ccs-vp.tau = ccs.tau

conv-reduces : forall {p1 c p2} -> ccs-vp.Reduces {penv} p1 c p2 -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) (conv-prog p2)
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
conv-reduces (ccs-vp.const r) = ccs.const (conv-reduces r)
conv-reduces (ccs-vp.rename {c} r) with c
... | ccs-vp.send _ _ = ccs.rename (conv-reduces r)
... | ccs-vp.recv _ _ = ccs.rename (conv-reduces r)
... | ccs-vp.tau      = ccs.rename (conv-reduces r)
conv-reduces (ccs-vp.hide {c} {z = z} r) with c
... | ccs-vp.send _ _ = ccs.hide {z = z} (conv-reduces r)
... | ccs-vp.recv _ _ = ccs.hide {z = z} (conv-reduces r)
... | ccs-vp.tau      = ccs.hide {z = z} (conv-reduces r)
conv-reduces (ccs-vp.if r) = ccs-real.indet (conv-reduces r)

unconv-reduces : forall {p1 c p2} -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) (conv-prog p2) -> ccs-vp.Reduces {penv} p1 c p2
unconv-reduces {op1} {oc} {op2} = helper {op1} {oc} {op2} refl refl refl
  where
  helper : forall {p1 rc p2} {cp1 cc cp2} -> cp1 ≡ conv-prog p1 -> cp2 ≡ conv-prog p2 -> cc ≡ conv-reduc-op rc
            -> ccs.Reduces cp1 cc cp2 -> ccs-vp.Reduces p1 rc p2
  -- helper {p1} {ccs-vp.send x x₁} {p2} {.(ccs.chan cc cp2)} {cc} {cp2} e1 e2 e3 ccs.chan = {! !}
  -- helper {p1} {ccs-vp.recv x x₁} {p2} {.(ccs.chan cc cp2)} {cc} {cp2} e1 e2 e3 ccs.chan = {!   !}
  -- helper {p1} {ccs-vp.tau} {p2} {.(ccs.chan cc cp2)} {cc} {cp2} e1 e2 e3 ccs.chan = {! !}
  -- helper {ccs-vp.par p1 p3} {rc} {ccs-vp.par p2 p4} {.(ccs.par (conv-prog p1) (conv-prog p3))} {.(conv-reduc-op rc)} {.(ccs.par _ (conv-prog p3))} refl e2 refl (ccs.par-L r) = {! !}
  -- helper {ccs-vp.par p1 p3} {rc} {ccs-vp.par p2 p4} {.(ccs.par (conv-prog p1) (conv-prog p3))} {.(conv-reduc-op rc)} {.(ccs.par (conv-prog p1) _)} refl e2 refl (ccs.par-R r) = {! !}
  -- helper {ccs-vp.par p1 p3} {rc} {ccs-vp.par p2 p4} {.(ccs.par (conv-prog p1) (conv-prog p3))} {.ccs.tau} {.(ccs.par (conv-prog p2) (conv-prog p4))} refl refl e3 (ccs.par-B r r₁) = {!  !}
  -- helper {ccs-vp.chan-recv x x₁} {rc} {p2} {.(ccs.indet (λ v → ccs.chan (ccs.recv (conv-c x v)) (conv-prog (x₁ v))))} {.(conv-reduc-op rc)} {.(conv-prog p2)} refl refl refl (ccs.indet r) = {!  !}
  -- helper {ccs-vp.indet f} {rc} {p2} {.(ccs.indet (\ s -> conv-prog (f s)))} {.(conv-reduc-op rc)} {.(conv-prog p2)} refl refl refl (ccs.indet r) = ccs-vp.indet (unconv-reduces r)
  -- helper {ccs-vp.if true p1} {rc} {p2} {.(ccs.indet (\ _ -> conv-prog p1))} {.(conv-reduc-op rc)} {.(conv-prog p2)} refl refl refl (ccs.indet r) = ccs-vp.if (unconv-reduces r)
  -- helper {ccs-vp.const n x} {rc} {p2} {.(ccs.const (conv-n n x))} {.(conv-reduc-op rc)} {.(conv-prog p2)} refl refl refl (ccs.const r) = ccs-vp.const (unconv-reduces r)
  -- helper {ccs-vp.rename x p1} {rc} {p2} {.(ccs.rename (conv-rename x) (conv-prog p1))} {.(ccs.map-chan-op (conv-rename x) _)} {.(ccs.rename (conv-rename x) _)} refl e2 e3 (ccs.rename r) = {! !}
  -- helper {ccs-vp.hide x p1} {rc} {p2} {.(ccs.hide (conv-hide x) (conv-prog p1))} {.(conv-reduc-op rc)} {.(ccs.hide (conv-hide x) _)} refl e2 refl (ccs.hide r) = {! !}
 
  helper {ccs-vp.indet _} refl refl refl (ccs.indet r) = ccs-vp.indet (unconv-reduces r)
  helper {ccs-vp.if true _} refl refl refl (ccs.indet r) = ccs-vp.if (unconv-reduces r)
  helper {ccs-vp.const _ _} refl refl refl (ccs.const r) = ccs-vp.const (unconv-reduces r)
  
  
  helper {ccs-vp.chan-send _ _ _} refl refl refl ccs.chan = ccs-vp.chan-send
  helper {ccs-vp.chan-recv _ _} refl refl refl ccs.chan = ccs-vp.chan-recv
  helper {ccs-vp.chan-tau _} refl refl refl ccs.chan = ccs-vp.chan-tau
  helper {ccs-vp.par _ _} refl refl refl (ccs.par-L r) = ccs-vp.par-L (unconv-reduces r)
  helper {ccs-vp.par _ _} refl refl refl (ccs.par-R r) = ccs-vp.par-R (unconv-reduces r)
  helper {ccs-vp.par _ _} refl refl refl (ccs.par-B r1 r2) = ccs-vp.par-L (unconv-reduces r1) (unconv-reduces r2)
  helper {ccs-vp.chan-recv _ _} refl refl refl (ccs.indet r) = unconv-reduces r
  helper {ccs-vp.rename _ _} refl refl refl (ccs.rename r) = ccs-vp.rename (unconv-reduces r)
  helper {ccs-vp.hide _ _} refl refl refl (ccs.hide r) = ccs-vp.hide (unconv-reduces r)
