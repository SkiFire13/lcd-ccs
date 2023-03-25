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
  {penv : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> ccs-vp.Proc {C} {N} {X} {V} {n-fv}}
  where

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

-- Now that we defined the needed types, open the modules with the correct values for the arguments
open ccs {Conv-C} {Conv-N} renaming (Reduces to ccs-Reduces)
open ccs-vp {C} {N} {X} {V} {n-fv} renaming (Reduces to ccs-vp-Reduces)

-- Convert a CCS-VP process to a normal CCS Process
-- the implementation is below, after a couple of helper co-recursive functions
conv-proc : ccs-vp.Proc -> ccs.Proc

conv-recv : C -> (V -> ccs-vp.Proc) -> V -> ccs.Proc
conv-recv c f = \ v -> chan (recv (conv-c c v)) (conv-proc (f v))

conv-indet : {S : Set} -> (S -> ccs-vp.Proc) -> S -> ccs.Proc
conv-indet f = \ s -> conv-proc (f s)

conv-rename : (C -> C) -> Conv-C -> Conv-C
conv-rename f = \ (conv-c c v) -> conv-c (f c) v

conv-hide : (C -> Bool) -> Conv-C -> Bool
conv-hide f = \ (conv-c c _) -> f c

conv-proc (chan-send c v p) = chan (send (conv-c c v)) (conv-proc p)
conv-proc (chan-recv c f) = indet (conv-recv c f)
conv-proc (chan-tau p) = chan (tau) (conv-proc p)
conv-proc (par p q) = par (conv-proc p) (conv-proc q)
conv-proc (indet f) = indet (conv-indet f)
conv-proc (const n args) = const (conv-n n args)
conv-proc (rename f p) = rename (conv-rename f) (conv-proc p)
conv-proc (hide f p) = hide (conv-hide f) (conv-proc p)
conv-proc (if b p) = if b then (conv-proc p) else ccs.deadlock

-- The converted process environment
conv-penv : ((conv-n n env) : Conv-N) -> ccs.Proc
conv-penv (conv-n n env) = conv-proc (penv n env)

-- Convert reduction operations in CCS-VP into channel operations in CCS
conv-reduc-op : ReducOp -> ChanOp
conv-reduc-op (send c v) = send (conv-c c v)
conv-reduc-op (recv c v) = recv (conv-c c v)
conv-reduc-op tau = tau

-- Convert a reduction relation from CCS-VP to CCS, or in other words,
-- prove that if there's a reduction relation between two CCS-VP processes
-- then there's a corresponding relation between the converted processess too.
conv-reduces : forall {p1 c p2} -> ccs-vp-Reduces {penv} p1 c p2
               -> ccs-Reduces {conv-penv} (conv-proc p1) (conv-reduc-op c) (conv-proc p2)
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

-- Prove that the converse of `conv-reduces` is not true, that is if there's
-- a reduction relation between two CCS processes then it's not guaranteed that
-- there's a reduction relation between CCS-VP processes that can be converted into them. 
unconv-need-exists : ¬ (forall {p1 c p2} -> ccs-Reduces {conv-penv} (conv-proc p1) (conv-reduc-op c) (conv-proc p2)
                     -> ccs-vp-Reduces {penv} p1 c p2)
unconv-need-exists f with f {chan-tau ccs-vp.deadlock} {tau} {if true ccs-vp.deadlock} chan
... | ()

-- Prove the less-strong version of the previous (false) theorem, that is
-- if a CCS-VP process converted to CCS has a relation with another CCS process
-- then there exists a corresponding relation between the initial CCS-VP process
-- and some other CCS-VP process that can be converted in the initial second CCS process.
unconv-reduces : forall {p1 c cp2} -> ccs-Reduces {conv-penv} (conv-proc p1) (conv-reduc-op c) cp2
                  -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × ccs-vp-Reduces {penv} p1 c p2)
unconv-reduces = helper refl refl
  where
  -- This helper is needed because Agda prefers plain variables when pattern matching rather
  -- the possible return values of a function.
  helper : forall {p1 c q1 cc cp2} -> q1 ≡ conv-proc p1 -> cc ≡ conv-reduc-op c -> ccs-Reduces {conv-penv} q1 cc cp2
           -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × ccs-vp-Reduces {penv} p1 c p2)
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
    -- Prove some guarantees about composing functions on channel/reduction operation that Agda can't prove.
    unconv-map-eq : forall {cc c f} -> map-chan-op (conv-rename f) cc ≡ conv-reduc-op c
                    -> ∃[ c' ] (cc ≡ conv-reduc-op c' × c ≡ map-reduc-op f c')
    unconv-map-eq {send (conv-c c v)} {send _ _} refl = send c v , refl , refl
    unconv-map-eq {recv (conv-c c v)} {recv _ _} refl = recv c v , refl , refl
    unconv-map-eq {tau} {tau} refl = tau , refl , refl
    -- Like `helper`, this function is only needed to introduce the additional `cc` variable.
    rename-helper : forall {f p1 c cc cp2} -> cc ≡ conv-reduc-op c
                    -> ccs-Reduces {conv-penv} (rename (conv-rename f) (conv-proc p1)) cc cp2
                    -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × ccs-vp-Reduces {penv} (rename f p1) c p2)
    rename-helper {f} {p1} e (rename r) with unconv-map-eq e
    ... | c' , refl , refl with unconv-reduces {p1} r
    ... | p' , refl , r' = rename f p' , refl , rename r'
  helper {hide f p1} {c} refl refl (hide {z = z} r) with unconv-reduces {p1} r
  ... | p' , refl , r' = hide f p' , refl , hide {z = unconv-z {f} {c} z} r'
    where
    -- This function is here only to give Agda a hint on which type we want to do unification.
    unconv-z : forall {f c} -> T (filter-chan-op (conv-hide f) (conv-reduc-op c)) -> T (filter-reduc-op f c)
    unconv-z {f} {send c _} _ with f c
    ... | true = tt
    unconv-z {f} {recv c _} _ with f c
    ... | true = tt
    unconv-z {f} {tau} _ = tt
  helper {if false p1} refl refl (indet {s = ()} r)
  helper {if true p1} refl refl r with unconv-reduces {p1} r
  ... | p' , refl , r' = p' , refl , if r'
