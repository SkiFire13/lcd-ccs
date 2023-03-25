open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Product

import ccs as ccs-real
import ccs-vp as ccs-vp-real

module conv
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

open ccs
open ccs-vp

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

conv-reduc-op : ccs-vp.ReducOp -> ccs.ChanOp
conv-reduc-op (send c v) = send (conv-c c v)
conv-reduc-op (recv c v) = recv (conv-c c v)
conv-reduc-op tau = tau

conv-reduces : forall {p1 c p2} -> ccs-vp.Reduces {penv} p1 c p2
                -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) (conv-prog p2)
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

unconv-need-exists : ¬ (forall {p1 c p2} -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) (conv-prog p2)
                      -> ccs-vp.Reduces {penv} p1 c p2)
unconv-need-exists f with f {chan-tau ccs-vp.deadlock} {tau} {if true ccs-vp.deadlock} chan
... | ()

unconv-reduces : forall {p1 c q2} -> ccs.Reduces {conv-penv} (conv-prog p1) (conv-reduc-op c) q2
                  -> ∃[ p2 ] (q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} p1 c p2)
unconv-reduces = helper refl refl
  where
  helper : forall {p1 c q1 cc q2} -> q1 ≡ conv-prog p1 -> cc ≡ conv-reduc-op c -> ccs.Reduces {conv-penv} q1 cc q2
            -> ∃[ p2 ] (q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} p1 c p2)
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
  helper {indet x} {c} refl refl (indet {s = s} r) with unconv-reduces {x s} {c} r
  ... | p' , refl , r' = p' , refl , indet {s = s} r'
  helper {const n x} {c} refl refl (const r) with unconv-reduces {penv n x} r
  ... | p' , refl , r' = p' , refl , const r'
  helper {rename x p1} {c} refl refl r = rename-helper refl r
    where
    unconv-map-eq : forall {cc c x} -> map-chan-op (conv-rename x) cc ≡ conv-reduc-op c
                      -> ∃[ c' ] (cc ≡ conv-reduc-op c' × c ≡ map-reduc-op x c')
    unconv-map-eq {send (conv-c c v)} {send _ _} refl = send c v , refl , refl
    unconv-map-eq {recv (conv-c c v)} {recv _ _} refl = recv c v , refl , refl
    unconv-map-eq {tau} {tau} refl = tau , refl , refl
    rename-helper : forall {x p1 c cc q2} -> cc ≡ conv-reduc-op c
                -> ccs.Reduces {conv-penv} (rename (conv-rename x) (conv-prog p1)) cc q2
                -> Σ[ p2 ∈ ccs-vp.Prog ] q2 ≡ conv-prog p2 × ccs-vp.Reduces {penv} (rename x p1) c p2
    rename-helper {x} {p1} e3 (rename r) with unconv-map-eq e3
    ... | c' , refl , refl with unconv-reduces {p1} r
    ... | p' , refl , r' = rename x p' , refl , rename r'
  helper {hide x p1} {c} refl refl (hide {z = z} r) with unconv-reduces {p1} r
  ... | p' , refl , r' = hide x p' , refl , hide {z = unconv-z {x} {c} z} r'
    where
    unconv-z : forall {x c} -> T (filter-chan-op (conv-hide x) (conv-reduc-op c)) -> T (filter-reduc-op x c)
    unconv-z {x} {send c _} t with x c
    ... | true = tt
    unconv-z {x} {recv c _} t with x c
    ... | true = tt
    unconv-z {x} {tau} t = tt
  helper {if false p1} refl refl (indet {s = ()} r)
  helper {if true p1} refl refl r with unconv-reduces {p1} r
  ... | p' , refl , r' = p' , refl , if r'
