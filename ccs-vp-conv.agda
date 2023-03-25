open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary.Decidable
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Function.Base

import ccs as ccs-real
import ccs-vp as ccs-vp-real

module ccs-vp-conv
  {C N X V : Set}
  {n-fv : N -> X -> Bool}
  {penv : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> ccs-vp-real.Prog {C} {N} {X} {V} {n-fv}}
  {v-proof : V}
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

conv-prog : ccs-vp.Prog -> ccs.Prog

conv-recv : C -> (V -> ccs-vp.Prog) -> V -> ccs.Prog
conv-recv c f v = ccs.chan (ccs.recv (conv-c c v)) (conv-prog (f v))

conv-indet : {S : Set} -> (S -> ccs-vp.Prog) -> S -> ccs.Prog
conv-indet f s = conv-prog (f s)

conv-rename : (C -> C) -> Conv-C -> Conv-C
conv-rename f (conv-c c v) = conv-c (f c) v

conv-hide : (C -> Bool) -> Conv-C -> Bool
conv-hide f (conv-c c _) = f c

conv-prog (ccs-vp.chan-send c v p) = ccs.chan (ccs.send (conv-c c v)) (conv-prog p)
conv-prog (ccs-vp.chan-recv c f) = ccs.indet (conv-recv c f)
conv-prog (ccs-vp.chan-tau p) = ccs.chan (ccs.tau) (conv-prog p)
conv-prog (ccs-vp.par p q) = ccs.par (conv-prog p) (conv-prog q)
conv-prog (ccs-vp.indet f) = ccs.indet (conv-indet f)
conv-prog (ccs-vp.const n args) = ccs.const (conv-n n args)
conv-prog (ccs-vp.rename f p) = ccs.rename (conv-rename f) (conv-prog p)
conv-prog (ccs-vp.hide f p) = ccs.hide (conv-hide f) (conv-prog p)
conv-prog (ccs-vp.if b p) = if b then (conv-prog p) else ccs.deadlock

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
conv-reduces (ccs-vp.if r) = conv-reduces r

-- unconv-reduces : forall {p1 c q2} -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) q2 -> Σ[ p2 ∈ ccs-vp.Prog ] q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} p1 c p2
-- unconv-reduces {op1} {oc} {oq2} or = helper {op1} {_} {oc} {_} {oq2} refl refl or
--   where
--   helper : forall {p1 q1 c cc q2} -> q1 ≡ conv-prog p1 -> cc ≡ conv-reduc-op c -> ccs.Reduces {conv-penv} q1 cc q2 -> Σ[ p2 ∈ ccs-vp.Prog ] q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} p1 c p2
--   helper {ccs-vp-real.chan-send x x₁ p1} {.(conv-prog (ccs-vp.chan-send x x₁ p1))} {ccs-vp-real.send .x .x₁} {.(conv-reduc-op (ccs-vp.send x x₁))} {.(conv-prog p1)} refl refl ccs-real.chan = {!   !}
--   helper {ccs-vp-real.chan-recv x x₁} {.(conv-prog (ccs-vp.chan-recv x x₁))} {ccs-vp-real.send x₂ x₃} {.(conv-reduc-op (ccs-vp.send x₂ x₃))} {q2} refl refl (ccs-real.indet ())
--   helper {ccs-vp-real.chan-recv x x₁} {.(conv-prog (ccs-vp.chan-recv x x₁))} {ccs-vp-real.recv .x x₃} {.(conv-reduc-op (ccs-vp.recv x x₃))} {.(conv-prog (x₁ x₃))} refl refl (ccs-real.indet ccs-real.chan) = {!   !}
--   helper {ccs-vp-real.chan-recv x x₁} {.(conv-prog (ccs-vp.chan-recv x x₁))} {ccs-vp-real.tau} {.(conv-reduc-op ccs-vp.tau)} {q2} refl refl (ccs-real.indet ())
--   helper {ccs-vp-real.chan-tau p1} {.(conv-prog (ccs-vp.chan-tau p1))} {ccs-vp-real.tau} {.(conv-reduc-op ccs-vp.tau)} {.(conv-prog p1)} refl refl ccs-real.chan = {!   !}
--   helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {ccs-vp-real.send x x₁} {.(conv-reduc-op (ccs-vp.send x x₁))} {.(ccs.par _ (conv-prog p2))} refl refl (ccs-real.par-L {p' = p'} r) = ccs-vp.par {!   !} p2 , {!   !}
--   helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {ccs-vp-real.send x x₁} {.(conv-reduc-op (ccs-vp.send x x₁))} {.(ccs.par (conv-prog p1) _)} refl refl (ccs-real.par-R {p' = p'} r) = {!   !}
--   helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {ccs-vp-real.recv x x₁} {.(conv-reduc-op (ccs-vp.recv x x₁))} {q2} refl refl r = {!   !}
--   helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {ccs-vp-real.tau} {.(conv-reduc-op ccs-vp.tau)} {q2} refl refl r = {!   !}
--   helper {ccs-vp-real.indet x} {.(conv-prog (ccs-vp.indet x))} {c} {.(conv-reduc-op c)} {q2} refl refl r = {!   !}
--   helper {ccs-vp-real.const n x} {.(conv-prog (ccs-vp.const n x))} {c} {.(conv-reduc-op c)} {q2} refl refl r = {!   !}
--   helper {ccs-vp-real.rename x p1} {.(conv-prog (ccs-vp.rename x p1))} {c} {.(conv-reduc-op c)} {q2} refl refl r = {!   !}
--   helper {ccs-vp-real.hide x p1} {.(conv-prog (ccs-vp.hide x p1))} {c} {.(conv-reduc-op c)} {q2} refl refl r = {!   !}
--   helper {ccs-vp-real.if x p1} {.(conv-prog (ccs-vp.if x p1))} {c} {.(conv-reduc-op c)} {q2} refl refl r = {!   !}


unconv-reduces : forall {p1 c q2} -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) q2 -> Σ[ p2 ∈ ccs-vp.Prog ] q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} p1 c p2
unconv-reduces {op1} {oc} {oq2} or = helper {op1} {_} {oc} {_} {oq2} refl refl or
  where
  helper : forall {p1 q1 c cc q2} -> q1 ≡ conv-prog p1 -> cc ≡ conv-reduc-op c -> ccs.Reduces {conv-penv} q1 cc q2 -> Σ[ p2 ∈ ccs-vp.Prog ] q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} p1 c p2
  helper {ccs-vp-real.chan-send x x₁ p1} {.(conv-prog (ccs-vp.chan-send x x₁ p1))} {ccs-vp-real.send .x .x₁} {ccs-real.send .(conv-c x x₁)} {.(conv-prog p1)} refl refl ccs-real.chan = {!   !}
  helper {ccs-vp-real.chan-recv x x₁} {.(conv-prog (ccs-vp.chan-recv x x₁))} {c} {cc} {q2} refl e2 r = {!   !}
  helper {ccs-vp-real.chan-tau p1} {.(conv-prog (ccs-vp.chan-tau p1))} {c} {cc} {q2} refl e2 r = {!   !}
  helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {c} {cc} {.(ccs.par _ (conv-prog p2))} refl e2 (ccs-real.par-L r) = {!   !}
  helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {c} {cc} {.(ccs.par (conv-prog p1) _)} refl e2 (ccs-real.par-R r) = {!   !}
  helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {ccs-vp-real.tau} {.(conv-reduc-op ccs-vp.tau)} {.(ccs.par pl' pr')} refl refl (ccs-real.par-B {c = ccs-real.send x} {pl' = pl'} {pr' = pr'} r r₁) with unconv-reduces {p1} r | unconv-reduces {p2} r₁
  ... | pl2 , refl , rl | pr2 , refl , rr = ccs-vp.par pl2 pr2 , refl , ccs-vp.par-B rl rr
  helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {ccs-vp-real.tau} {.(conv-reduc-op ccs-vp.tau)} {.(ccs.par pl' pr')} refl refl (ccs-real.par-B {c = ccs-real.recv x} {pl' = pl'} {pr' = pr'} r r₁) with unconv-reduces {p1} r | unconv-reduces {p2} r₁
  ... | pl2 , refl , rl | pr2 , refl , rr = ccs-vp.par pl2 pr2 , refl , ccs-vp.par-B rl rr
  helper {ccs-vp-real.par p1 p2} {.(conv-prog (ccs-vp.par p1 p2))} {ccs-vp-real.tau} {.(conv-reduc-op ccs-vp.tau)} {.(ccs.par pl' pr')} refl refl (ccs-real.par-B {c = ccs-real.tau} {pl' = pl'} {pr' = pr'} r r₁) with unconv-reduces {p1} r | unconv-reduces {p2} r₁
  ... | pl2 , refl , rl | pr2 , refl , rr = ccs-vp.par pl2 pr2 , refl , ccs-vp.par-B rl rr
  helper {ccs-vp-real.indet x} {.(conv-prog (ccs-vp.indet x))} {c} {.(conv-reduc-op c)} {q2} refl refl (ccs-real.indet r) = {!   !}
  helper {ccs-vp-real.const n x} {.(conv-prog (ccs-vp.const n x))} {c} {cc} {q2} refl e2 r = {!   !}
  helper {ccs-vp-real.rename x p1} {.(conv-prog (ccs-vp.rename x p1))} {c} {cc} {q2} refl e2 r = {!   !}
  helper {ccs-vp-real.hide x p1} {.(conv-prog (ccs-vp.hide x p1))} {c} {cc} {q2} refl e2 r = {!   !}
  helper {ccs-vp-real.if x p1} {.(conv-prog (ccs-vp.if x p1))} {c} {cc} {q2} refl e2 r = {!   !}
 