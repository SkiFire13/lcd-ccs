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

unconv-need-exists : (forall {p1 c p2} -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) (conv-prog p2)
                      -> ccs-vp.Reduces {penv} p1 c p2) -> ⊥
unconv-need-exists f = impossible (f ccs.chan)
  where
  impossible : ccs-vp.Reduces {penv} (ccs-vp.chan-tau ccs-vp.deadlock) ccs-vp.tau (ccs-vp.if true ccs-vp.deadlock) -> ⊥
  impossible ()

unconv-z : forall {x c} -> T (ccs.filter-chan-op (conv-hide x) (conv-reduc-op c)) -> T (ccs-vp.filter-reduc-op x c)
unconv-z {x} {ccs-vp-real.send c _} t with x c
... | true = tt
unconv-z {x} {ccs-vp-real.recv c _} t with x c
... | true = tt
unconv-z {x} {ccs-vp-real.tau} t = tt

unconv-map-eq : forall {cc c x} -> ccs.map-chan-op (conv-rename x) cc ≡ conv-reduc-op c
                  -> Σ[ c' ∈ ccs-vp.ReducOp ] cc ≡ conv-reduc-op c' × c ≡ ccs-vp.map-reduc-op x c'
unconv-map-eq {ccs.send (conv-c c v)} {ccs-vp.send _ _} refl = ccs-vp.send c v , refl , refl
unconv-map-eq {ccs.recv (conv-c c v)} {ccs-vp.recv _ _} refl = ccs-vp.recv c v , refl , refl
unconv-map-eq {ccs.tau} {ccs-vp.tau} refl = ccs-vp.tau , refl , refl

unconv-reduces : forall {p1 c q2} -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) q2
                  -> Σ[ p2 ∈ ccs-vp.Prog ] q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} p1 c p2
unconv-reduces {op1} {oc} {oq2} or = helper {op1} {oc} {_} {_} {oq2} refl refl or
  where
  helper : forall {p1 c q1 cc q2} -> q1 ≡ conv-prog p1 -> cc ≡ conv-reduc-op c -> ccs.Reduces {conv-penv} q1 cc q2
            -> Σ[ p2 ∈ ccs-vp.Prog ] q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} p1 c p2
  helper {ccs-vp.chan-send _ _ p1} {ccs-vp.send _ _} refl refl ccs.chan = p1 , refl , ccs-vp.chan-send
  helper {ccs-vp.chan-recv _ f} {ccs-vp.recv _ v} refl refl (ccs.indet ccs.chan) = f v , refl , ccs-vp.chan-recv
  helper {ccs-vp.chan-tau p1} {ccs-vp.tau} refl refl ccs.chan = p1 , refl , ccs-vp.chan-tau
  helper {ccs-vp.par p1 p2} {c} refl e2 (ccs.par-L r) with helper {p1} {c} refl e2 r
  ... | p' , refl , r' = ccs-vp.par p' p2 , refl , ccs-vp.par-L r'
  helper {ccs-vp.par p1 p2} {c} refl e2 (ccs.par-R r) with helper {p2} {c} refl e2 r
  ... | p' , refl , r' = ccs-vp.par p1 p' , refl , ccs-vp.par-R r'
  helper {ccs-vp.par p1 p2} {ccs-vp.tau} refl refl (ccs.par-B {ccs.send _} r1 r2) with
    unconv-reduces {p1} r1 | unconv-reduces {p2} r2
  ... | pl' , refl , rl | pr' , refl , rr = ccs-vp.par pl' pr' , refl , ccs-vp.par-B rl rr
  helper {ccs-vp.par p1 p2} {ccs-vp.tau} refl refl (ccs.par-B {ccs.recv _} r1 r2) with
    unconv-reduces {p1} r1 | unconv-reduces {p2} r2
  ... | pl' , refl , rl | pr' , refl , rr = ccs-vp.par pl' pr' , refl , ccs-vp.par-B rl rr
  helper {ccs-vp.par p1 p2} {ccs-vp.tau} refl refl (ccs.par-B {ccs.tau} r1 r2) with
    unconv-reduces {p1} r1 | unconv-reduces {p2} r2
  ... | pl' , refl , rl | pr' , refl , rr = ccs-vp.par pl' pr' , refl , ccs-vp.par-B rl rr
  helper {ccs-vp.indet x} {c} refl refl (ccs.indet {s = s} r) with unconv-reduces {x s} {c} r
  ... | p' , refl , r' = p' , refl , ccs-vp.indet {s = s} r'
  helper {ccs-vp.const n x} {c} refl refl (ccs.const r) with unconv-reduces {penv n x} r
  ... | p' , refl , r' = p' , refl , ccs-vp.const r'
  helper {ccs-vp.rename x p1} {c} refl refl r = helper' refl refl refl r
    where
    helper' : forall {x p1 c mc f cc q2} -> mc ≡ ccs.map-chan-op f cc -> f ≡ conv-rename x -> cc ≡ conv-reduc-op c
                -> ccs.Reduces {conv-penv} (ccs.rename f (conv-prog p1)) cc q2
                -> Σ[ p2 ∈ ccs-vp.Prog ] q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} (ccs-vp.rename x p1) c p2
    helper' {x} {p1} refl refl e3 (ccs.rename r) with unconv-map-eq e3
    ... | c' , refl , refl with unconv-reduces {p1} r
    ... | p' , refl , r' = ccs-vp.rename x p' , refl , ccs-vp.rename r'
  helper {ccs-vp.hide x p1} {c} refl refl (ccs.hide {z = z} r) with unconv-reduces {p1} r
  ... | p' , refl , r' = ccs-vp.hide x p' , refl , ccs-vp.hide {z = unconv-z {x} {c} z} r'
  helper {ccs-vp.if false p1} refl refl (ccs.indet {s = ()} r)
  helper {ccs-vp.if true p1} refl refl r with unconv-reduces {p1} r
  ... | p' , refl , r' = p' , refl , ccs-vp.if r'
