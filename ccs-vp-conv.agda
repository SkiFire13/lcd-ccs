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

conv-prog : ccs-vp.Prog -> ccs.Prog

conv-recv : C -> (V -> ccs-vp.Prog) -> V -> ccs.Prog
conv-recv c f v = ccs.chan (ccs.recv (conv-c c v)) (conv-prog (f v))

conv-indet : {S : Set} -> (S -> ccs-vp.Prog) -> S -> ccs.Prog
conv-indet f s = conv-prog (f s)

conv-rename : (C -> C) -> Conv-C -> Conv-C
conv-rename f (conv-c c v) = conv-c (f c) v

conv-hide : (C -> Bool) -> Conv-C -> Bool
conv-hide f (conv-c c _) = f c

conv-if : ccs-vp.Prog -> {S : Set} -> S -> ccs.Prog
conv-if p _ = conv-prog p

conv-prog (ccs-vp.chan-send c v p) = ccs.chan (ccs.send (conv-c c v)) (conv-prog p)
conv-prog (ccs-vp.chan-recv c f) = ccs.indet (conv-recv c f)
conv-prog (ccs-vp.chan-tau p) = ccs.chan (ccs.tau) (conv-prog p)
conv-prog (ccs-vp.par p q) = ccs.par (conv-prog p) (conv-prog q)
conv-prog (ccs-vp.indet f) = ccs.indet (conv-indet f)
conv-prog (ccs-vp.const n args) = ccs.const (conv-n n args)
conv-prog (ccs-vp.rename f p) = ccs.rename (conv-rename f) (conv-prog p)
conv-prog (ccs-vp.hide f p) = ccs.hide (conv-hide f) (conv-prog p)
conv-prog (ccs-vp.if b p) = ccs.indet {S = if b then ⊤ else ⊥} (conv-if p)

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

-- IDEA : Wrap V/Bool when desugaring to indet

conv-rename-eq : forall {f1} {f2} -> conv-rename f1 ≡ conv-rename f2 -> f1 ≡ f2
conv-rename-eq {f1} {f2} eq = {!   !}

conv-hide-eq : forall {f1} {f2} -> conv-hide f1 ≡ conv-hide f2 -> f1 ≡ f2
conv-hide-eq {f1} {f2} eq = {!   !}

conv-prog-eq : forall {p q} -> conv-prog p ≡ conv-prog q -> p ≡ q
conv-prog-eq {ccs-vp-real.chan-send x x₁ p} {ccs-vp-real.chan-send x₂ x₃ q} eq with ccs.chan-eq-c eq | conv-prog-eq (ccs.chan-eq-p eq)
... | refl | refl = refl
conv-prog-eq {ccs-vp-real.chan-recv x x₁} {ccs-vp-real.chan-recv x₂ x₃} eq = {!  !}
conv-prog-eq {ccs-vp-real.chan-recv x x₁} {ccs-vp-real.indet x₂} eq = {!   !}
conv-prog-eq {ccs-vp-real.chan-recv x x₁} {ccs-vp-real.if x₂ q} eq = {!   !}
conv-prog-eq {ccs-vp-real.chan-tau p} {ccs-vp-real.chan-tau q} eq with ccs.chan-eq-c eq | conv-prog-eq (ccs.chan-eq-p eq)
... | refl | refl = refl
conv-prog-eq {ccs-vp-real.par p p₁} {ccs-vp-real.par q q₁} eq with conv-prog-eq (ccs.par-eq-l eq) | conv-prog-eq (ccs.par-eq-r eq)
... | refl | refl = refl
conv-prog-eq {ccs-vp-real.indet x} {ccs-vp-real.chan-recv x₁ x₂} eq = {!   !}
conv-prog-eq {ccs-vp-real.indet x} {ccs-vp-real.indet x₁} eq = {!   !}
conv-prog-eq {ccs-vp-real.indet x} {ccs-vp-real.if x₁ q} eq = {!   !}
conv-prog-eq {ccs-vp-real.const n x} {ccs-vp-real.const n₁ x₁} eq with ccs.const-eq-n eq
... | refl = refl
conv-prog-eq {ccs-vp-real.rename x p} {ccs-vp-real.rename x₁ q} eq with conv-rename-eq (ccs.rename-eq-f eq) | conv-prog-eq (ccs.rename-eq-p eq)
... | refl | refl = refl
conv-prog-eq {ccs-vp-real.hide x p} {ccs-vp-real.hide x₁ q} eq  with conv-hide-eq (ccs.hide-eq-f eq) | conv-prog-eq (ccs.hide-eq-p eq)
... | refl | refl = refl
conv-prog-eq {ccs-vp-real.if x p} {ccs-vp-real.chan-recv x₁ x₂} eq with x | ccs.indet-eq-S eq
conv-prog-eq {ccs-vp-real.if false p} {ccs-vp-real.chan-recv x₁ x₂} eq | true | refl = {!  !}
conv-prog-eq {ccs-vp-real.if true p} {ccs-vp-real.chan-recv x₁ x₂} eq | true | refl = {!   !}
conv-prog-eq {ccs-vp-real.if false p} {ccs-vp-real.chan-recv x₁ x₂} eq | false | refl = {!   !}
conv-prog-eq {ccs-vp-real.if true p} {ccs-vp-real.chan-recv x₁ x₂} eq | false | refl = {!   !}
conv-prog-eq {ccs-vp-real.if x p} {ccs-vp-real.indet x₁} eq = {!   !}
conv-prog-eq {ccs-vp-real.if x p} {ccs-vp-real.if x₁ q} eq = {!   !}

unconv-reduces : forall {p1 c p2} -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) (conv-prog p2) -> ccs-vp.Reduces {penv} p1 c p2
unconv-reduces {op1} {oc} {op2} = helper {op1} {oc} {op2} refl refl refl
  where
  helper : forall {p1 rc p2} {cp1 cc cp2} -> cp1 ≡ conv-prog p1 -> cp2 ≡ conv-prog p2 -> cc ≡ conv-reduc-op rc
            -> ccs.Reduces cp1 cc cp2 -> ccs-vp.Reduces p1 rc p2
  helper {ccs-vp-real.chan-send x₂ x₃ p1} {ccs-vp-real.send .x₂ .x₃} {p2} {.(conv-prog (ccs-vp.chan-send x₂ x₃ p1))} {.(ccs.send (conv-c x₂ x₃))} {.(conv-prog p1)} refl e2 refl ccs-real.chan = {!  !}
  helper {ccs-vp-real.chan-tau p1} {ccs-vp-real.send x x₁} {p2} {.(conv-prog (ccs-vp.chan-tau p1))} {.ccs.tau} {.(conv-prog p1)} refl e2 () ccs-real.chan
  helper {ccs-vp-real.chan-send x₂ x₃ p1} {ccs-vp-real.recv x x₁} {p2} {.(conv-prog (ccs-vp.chan-send x₂ x₃ p1))} {.(ccs.send (conv-c x₂ x₃))} {.(conv-prog p1)} refl e2 () ccs-real.chan
  helper {ccs-vp-real.chan-tau p1} {ccs-vp-real.recv x x₁} {p2} {.(conv-prog (ccs-vp.chan-tau p1))} {.ccs.tau} {.(conv-prog p1)} refl e2 () ccs-real.chan
  helper {p1} {ccs-vp.tau} {p2} {.(ccs.chan cc cp2)} {cc} {cp2} e1 e2 e3 ccs.chan = {! !}
  helper {ccs-vp.par p1 p3} {rc} {ccs-vp.par p2 p4} {.(ccs.par (conv-prog p1) (conv-prog p3))} {.(conv-reduc-op rc)} {.(ccs.par _ (conv-prog p3))} refl e2 refl (ccs.par-L r) with ccs.par-eq-l e2 | ccs.par-eq-r e2
  ... | refl | eq = {!  !}
  helper {ccs-vp.par p1 p3} {rc} {ccs-vp.par p2 p4} {.(ccs.par (conv-prog p1) (conv-prog p3))} {.(conv-reduc-op rc)} {.(ccs.par (conv-prog p1) _)} refl e2 refl (ccs.par-R r) = {! !}
  helper {ccs-vp-real.par p1 p3} {ccs-vp-real.tau} {ccs-vp-real.par p2 p4} {.(ccs-real.par (conv-prog p1) (conv-prog p3))} {.ccs-real.tau} {.(ccs-real.par (conv-prog p2) (conv-prog p4))} refl refl refl (ccs-real.par-B {c} r r₁) with c
  ... | ccs.send _ = ccs-vp.par-B (unconv-reduces r) (unconv-reduces r₁)
  ... | ccs.recv _ = ccs-vp.par-B (unconv-reduces r) (unconv-reduces r₁)
  ... | ccs.tau    = ccs-vp.par-B (unconv-reduces r) (unconv-reduces r₁)
  helper {ccs-vp-real.chan-recv x x₁} {ccs-vp-real.recv x₂ x₃} {p2} {.(ccs.indet (conv-recv x x₁))} {.(conv-reduc-op (ccs-vp.recv x₂ x₃))} {.(conv-prog p2)} refl refl refl (ccs-real.indet r) = {!  !}
  helper {ccs-vp.indet f} {rc} {p2} {.(ccs.indet (conv-indet f))} {.(conv-reduc-op rc)} {.(conv-prog p2)} refl refl refl (ccs.indet r) = ccs-vp.indet (unconv-reduces r)
  helper {ccs-vp.if true p1} {rc} {p2} {.(ccs.indet (conv-if p1))} {.(conv-reduc-op rc)} {.(conv-prog p2)} refl refl refl (ccs.indet r) = ccs-vp.if (unconv-reduces r)
  helper {ccs-vp.const n x} {rc} {p2} {.(ccs.const (conv-n n x))} {.(conv-reduc-op rc)} {.(conv-prog p2)} refl refl refl (ccs.const r) = ccs-vp.const (unconv-reduces r)
  helper {ccs-vp-real.rename x p1} {ccs-vp-real.send x₂ x₃} {ccs-vp-real.rename x₁ p2} {.(ccs-real.rename (conv-rename x) (conv-prog p1))} {.(ccs-real.send (conv-c (x chan) value))} {.(ccs-real.rename (conv-rename x) _)} refl e2 e3 (ccs-real.rename {ccs-real.send (conv-c chan value)} r) = {!  !}
  helper {ccs-vp-real.rename x p1} {ccs-vp-real.recv x₂ x₃} {ccs-vp-real.rename x₁ p2} {.(ccs-real.rename (conv-rename x) (conv-prog p1))} {.(ccs-real.recv (conv-c (x chan) value))} {.(ccs-real.rename (conv-rename x) _)} refl e2 e3 (ccs-real.rename {ccs-real.recv (conv-c chan value)} r) = {!  !}
  helper {ccs-vp-real.rename x p1} {ccs-vp-real.tau} {ccs-vp-real.rename x₁ p2} {.(ccs-real.rename (conv-rename x) (conv-prog p1))} {.ccs-real.tau} {.(ccs-real.rename (conv-rename x) _)} refl e2 e3 (ccs-real.rename {ccs-real.tau} r) = {!  !}
  helper {ccs-vp-real.hide x p1} {rc} {ccs-vp-real.hide x₁ p2} {.(ccs-real.hide (conv-hide x) (conv-prog p1))} {.(conv-reduc-op rc)} {.(ccs-real.hide (conv-hide x) _)} refl e2 refl (ccs-real.hide {q = _} {z = z} r) with (ccs.filter-chan-op (conv-hide x) (conv-reduc-op rc))
  helper {ccs-vp-real.hide x p1} {rc} {ccs-vp-real.hide x₁ p2} {.(conv-prog (ccs-vp-real.hide x p1))} {.(conv-reduc-op rc)} {ccs-real.hide .(conv-hide x) _} refl e2 refl (ccs-real.hide {q = q} {z = tt} r) | true = {!   !}
  helper {ccs-vp-real.hide x p1} {rc} {ccs-vp-real.hide x₁ p2} {.(conv-prog (ccs-vp-real.hide x p1))} {.(conv-reduc-op rc)} {ccs-real.hide .(conv-hide x) _} refl e2 refl (ccs-real.hide {q = q} {z = ()} r) | false
 
  -- helper {ccs-vp.indet _} refl refl refl (ccs.indet r) = ccs-vp.indet (unconv-reduces r)
  -- helper {ccs-vp.if true _} refl refl refl (ccs.indet r) = ccs-vp.if (unconv-reduces r)
  -- helper {ccs-vp.const _ _} refl refl refl (ccs.const r) = ccs-vp.const (unconv-reduces r)
  
  -- helper {ccs-vp.chan-send _ _ _} {ccs-vp.send _ _} refl refl refl ccs.chan = ccs-vp.chan-send
  -- helper {ccs-vp.chan-tau _} refl refl refl ccs.chan = ccs-vp.chan-tau
  -- helper {ccs-vp.par _ _} refl refl refl (ccs.par-L r) = ccs-vp.par-L (unconv-reduces r)
  -- helper {ccs-vp.par _ _} refl refl refl (ccs.par-R r) = ccs-vp.par-R (unconv-reduces r)
  -- helper {ccs-vp.par _ _} refl refl refl (ccs.par-B r1 r2) = ccs-vp.par-L (unconv-reduces r1) (unconv-reduces r2)
  -- helper {ccs-vp.chan-recv _ _} refl refl refl (ccs.indet ccs.chan) = ccs-vp.chan-recv
  -- helper {ccs-vp.rename _ _} refl refl refl (ccs.rename r) = ccs-vp.rename (unconv-reduces r)
  -- helper {ccs-vp.hide _ _} refl refl refl (ccs.hide r) = ccs-vp.hide (unconv-reduces r)
   