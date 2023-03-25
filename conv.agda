open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Product

import ccs
import ccs-vp

module conv
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


open ccs {Conv-C} {Conv-N}
open ccs-vp {C} {N} {X} {V} {n-fv}

conv-prog : ccs-vp.Prog -> ccs.Prog

conv-recv : C -> (V -> ccs-vp.Prog) -> V -> ccs.Prog
conv-recv c f v = chan (recv (conv-c c v)) (conv-prog (f v))

conv-indet : {S : Set} -> (S -> ccs-vp.Prog) -> S -> ccs.Prog
conv-indet f s = conv-prog (f s)

conv-rename : (C -> C) -> Conv-C -> Conv-C
conv-rename f (conv-c c v) = conv-c (f c) v

conv-hide : (C -> Bool) -> Conv-C -> Bool
conv-hide f (conv-c c _) = f c

conv-prog (chan-send c v p) = chan (send (conv-c c v)) (conv-prog p)
conv-prog (chan-recv c f) = indet (conv-recv c f)
conv-prog (chan-tau p) = chan (tau) (conv-prog p)
conv-prog (par p q) = par (conv-prog p) (conv-prog q)
conv-prog (indet f) = indet (conv-indet f)
conv-prog (const n args) = const (conv-n n args)
conv-prog (rename f p) = rename (conv-rename f) (conv-prog p)
conv-prog (hide f p) = hide (conv-hide f) (conv-prog p)
conv-prog (if b p) = if b then (conv-prog p) else ccs.deadlock

conv-penv : ((conv-n n env) : Conv-N) -> ccs.Prog
conv-penv (conv-n n env) = conv-prog (penv n env)

conv-reduc-op : ReducOp -> ChanOp
conv-reduc-op (send c v) = send (conv-c c v)
conv-reduc-op (recv c v) = recv (conv-c c v)
conv-reduc-op tau = tau

ccs-Reduces = ccs.Reduces {Conv-C} {Conv-N} {conv-penv}
ccs-vp-Reduces = ccs-vp.Reduces {C} {N} {X} {V} {n-fv} {penv}

conv-reduces : forall {p1 c p2} -> ccs-vp-Reduces p1 c p2
                -> ccs-Reduces (conv-prog p1) (conv-reduc-op c) (conv-prog p2)
conv-reduces chan-send = chan
conv-reduces chan-recv = indet chan
conv-reduces chan-tau = chan
conv-reduces (par-L r) = par-L (conv-reduces r)
conv-reduces (par-R r) = par-R (conv-reduces r)
conv-reduces (par-B {c} rl rr) with c
... | send _ _ = par-B (conv-reduces rl) (conv-reduces rr)
... | recv _ _ = par-B (conv-reduces rl) (conv-reduces rr)
... | tau      = par-B (conv-reduces rl) (conv-reduces rr)
conv-reduces (indet r) = indet (conv-reduces r)
conv-reduces (const r) = const (conv-reduces r)
conv-reduces (rename {c} r) with c
... | send _ _ = rename (conv-reduces r)
... | recv _ _ = rename (conv-reduces r)
... | tau      = rename (conv-reduces r)
conv-reduces (hide {c} {z = z} r) with c
... | send _ _ = hide {z = z} (conv-reduces r)
... | recv _ _ = hide {z = z} (conv-reduces r)
... | tau      = hide {z = z} (conv-reduces r)
conv-reduces (if r) = conv-reduces r

unconv-need-exists : ¬ (forall {p1 c p2} -> ccs-Reduces (conv-prog p1) (conv-reduc-op c) (conv-prog p2)
                      -> ccs-vp-Reduces p1 c p2)
unconv-need-exists f with f {chan-tau ccs-vp.deadlock} {tau} {if true ccs-vp.deadlock} chan
... | ()

unconv-reduces : forall {p1 c cp2} -> ccs-Reduces (conv-prog p1) (conv-reduc-op c) cp2
                  -> ∃[ p2 ] (cp2 ≡ conv-prog p2 × ccs-vp-Reduces p1 c p2)
unconv-reduces = helper refl refl
  where
  helper : forall {p1 c q1 cc cp2} -> q1 ≡ conv-prog p1 -> cc ≡ conv-reduc-op c -> ccs-Reduces q1 cc cp2
            -> ∃[ p2 ] (cp2 ≡ conv-prog p2 × ccs-vp-Reduces p1 c p2)
  helper {chan-send _ _ p1} {send _ _} refl refl chan = p1 , refl , chan-send
  helper {chan-recv _ f} {recv _ v} refl refl (indet chan) = f v , refl , chan-recv
  helper {chan-tau p1} {tau} refl refl chan = p1 , refl , chan-tau
  helper {par pl pr} {c} refl e2 (par-L r) with helper {pl} {c} refl e2 r
  ... | p' , refl , r' = par p' pr , refl , par-L r'
  helper {par pl pr} {c} refl e2 (par-R r) with helper {pr} {c} refl e2 r
  ... | p' , refl , r' = par pl p' , refl , par-R r'
  helper {par pl pr} {tau} refl refl (par-B {send _} r1 r2) with unconv-reduces {pl} r1 | unconv-reduces {pr} r2
  ... | pl' , refl , rl | pr' , refl , rr = par pl' pr' , refl , par-B rl rr
  helper {par pl pr} {tau} refl refl (par-B {recv _} r1 r2) with unconv-reduces {pl} r1 | unconv-reduces {pr} r2
  ... | pl' , refl , rl | pr' , refl , rr = par pl' pr' , refl , par-B rl rr
  helper {par pl pr} {tau} refl refl (par-B {tau} r1 r2) with unconv-reduces {pl} r1 | unconv-reduces {pr} r2
  ... | pl' , refl , rl | pr' , refl , rr = par pl' pr' , refl , par-B rl rr
  helper {indet f} {c} refl refl (indet {s = s} r) with unconv-reduces {f s} {c} r
  ... | p' , refl , r' = p' , refl , indet {s = s} r'
  helper {const n args} {c} refl refl (const r) with unconv-reduces {penv n args} r
  ... | p' , refl , r' = p' , refl , const r'
  helper {rename f p1} {c} refl refl r = rename-helper refl r
    where
    unconv-map-eq : forall {cc c f} -> map-chan-op (conv-rename f) cc ≡ conv-reduc-op c
                      -> ∃[ c' ] (cc ≡ conv-reduc-op c' × c ≡ map-reduc-op f c')
    unconv-map-eq {send (conv-c c v)} {send _ _} refl = send c v , refl , refl
    unconv-map-eq {recv (conv-c c v)} {recv _ _} refl = recv c v , refl , refl
    unconv-map-eq {tau} {tau} refl = tau , refl , refl
    rename-helper : forall {f p1 c cc cp2} -> cc ≡ conv-reduc-op c
                -> ccs-Reduces (rename (conv-rename f) (conv-prog p1)) cc cp2
                -> ∃[ p2 ] (cp2 ≡ conv-prog p2 × ccs-vp-Reduces (rename f p1) c p2)
    rename-helper {f} {p1} e (rename r) with unconv-map-eq e
    ... | c' , refl , refl with unconv-reduces {p1} r
    ... | p' , refl , r' = rename f p' , refl , rename r'
  helper {hide f p1} {c} refl refl (hide {z = z} r) with unconv-reduces {p1} r
  ... | p' , refl , r' = hide f p' , refl , hide {z = unconv-z {f} {c} z} r'
    where
    unconv-z : forall {f c} -> T (filter-chan-op (conv-hide f) (conv-reduc-op c)) -> T (filter-reduc-op f c)
    unconv-z {f} {send c _} _ with f c
    ... | true = tt
    unconv-z {f} {recv c _} _ with f c
    ... | true = tt
    unconv-z {f} {tau} _ = tt
  helper {if false p1} refl refl (indet {s = ()} r)
  helper {if true p1} refl refl r with unconv-reduces {p1} r
  ... | p' , refl , r' = p' , refl , if r'
