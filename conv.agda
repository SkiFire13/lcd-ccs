open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Empty
open import Data.Unit
open import Data.Product

import ccs
import ccs-vp as vp

module conv
  {C N X V : Set}
  {n-fv : N -> X -> Bool}
  {penv : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> vp.Proc {C} {N} {X} {V} {n-fv}}
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
open ccs {Conv-C} {Conv-N} renaming (Reduc to ccs-Reduc; Act to ccs-Act)
open vp {C} {N} {X} {V} {n-fv} renaming (Reduc to vp-Reduc; Act to vp-Act)

-- Convert a CCS-VP process to a normal CCS Process
-- the implementation is below, after a couple of helper co-recursive functions
conv-proc : vp.Proc -> ccs.Proc

conv-recv : C -> (V -> vp.Proc) -> V -> ccs.Proc
conv-recv c f = \ v -> chan (recv (conv-c c v)) (conv-proc (f v))

conv-indet : {S : Set} -> (S -> vp.Proc) -> S -> ccs.Proc
conv-indet f = \ s -> conv-proc (f s)

conv-rename : (C -> C) -> Conv-C -> Conv-C
conv-rename f = \ (conv-c c v) -> conv-c (f c) v

conv-hide : (C -> Bool) -> Conv-C -> Bool
conv-hide f = \ (conv-c c _) -> f c

conv-proc (chan-send c v p) = chan (send (conv-c c v)) (conv-proc p)
conv-proc (chan-recv c f)   = indet (conv-recv c f)
conv-proc (chan-tau p)      = chan (tau) (conv-proc p)
conv-proc (par p q)         = par (conv-proc p) (conv-proc q)
conv-proc (indet f)         = indet (conv-indet f)
conv-proc (const n args)    = const (conv-n n args)
conv-proc (rename f p)      = rename (conv-rename f) (conv-proc p)
conv-proc (hide f p)        = hide (conv-hide f) (conv-proc p)
conv-proc (if b p)          = if b then (conv-proc p) else ccs.deadlock

-- The converted process environment
conv-penv : ((conv-n n env) : Conv-N) -> ccs.Proc
conv-penv (conv-n n env) = conv-proc (penv n env)

-- Convert reduction operations in CCS-VP into channel operations in CCS
conv-act : vp-Act -> ccs-Act
conv-act (send c v) = send (conv-c c v)
conv-act (recv c v) = recv (conv-c c v)
conv-act tau = tau

-- Convert a reduction relation from CCS-VP to CCS, or in other words,
-- prove that if there's a reduction relation between two CCS-VP processes
-- then there's a corresponding relation between the converted processess too.
conv-reduc : forall {p1 c p2} -> vp-Reduc {penv} p1 c p2
               -> ccs-Reduc {conv-penv} (conv-proc p1) (conv-act c) (conv-proc p2)
conv-reduc chan-send = chan
conv-reduc chan-recv = indet chan
conv-reduc chan-tau  = chan
conv-reduc (par-L r) = par-L (conv-reduc r)
conv-reduc (par-R r) = par-R (conv-reduc r)
conv-reduc (par-B {c} rl rr) with c
... | send _ _       = par-B (conv-reduc rl) (conv-reduc rr)
... | recv _ _       = par-B (conv-reduc rl) (conv-reduc rr)
... | tau            = par-B (conv-reduc rl) (conv-reduc rr)
conv-reduc (indet r) = indet (conv-reduc r)
conv-reduc (const r) = const (conv-reduc r)
conv-reduc (rename {c} r) with c
... | send _ _       = rename (conv-reduc r)
... | recv _ _       = rename (conv-reduc r)
... | tau            = rename (conv-reduc r)
conv-reduc (hide {c} {z = z} r) with c
... | send _ _       = hide {z = z} (conv-reduc r)
... | recv _ _       = hide {z = z} (conv-reduc r)
... | tau            = hide {z = z} (conv-reduc r)
conv-reduc (if r)    = conv-reduc r

-- Prove that the converse of `conv-reduc` is not true, that is if there's
-- a reduction relation between two CCS processes then it's not guaranteed that
-- there's a reduction relation between CCS-VP processes that can be converted into them. 
NaiveUnconv : Set₁
NaiveUnconv = forall {p1 c p2} 
  -> ccs-Reduc {conv-penv} (conv-proc p1) (conv-act c) (conv-proc p2)
  -> vp-Reduc {penv} p1 c p2

unconv-need-exists : ¬ NaiveUnconv
unconv-need-exists f with f {chan-tau vp.deadlock} {tau} {if true vp.deadlock} chan
... | ()

-- Prove the less-strong version of the previous (false) theorem, that is
-- if a CCS-VP process converted to CCS has a relation with another CCS process
-- then there exists a corresponding relation between the initial CCS-VP process
-- and some other CCS-VP process that can be converted in the initial second CCS process.
unconv-reduc : forall {p1 c cp2} 
                 -> ccs-Reduc {conv-penv} (conv-proc p1) (conv-act c) cp2
                 -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp-Reduc {penv} p1 c p2)
unconv-reduc = helper refl refl
  where
  -- This helper is needed because Agda prefers plain variables when pattern matching rather
  -- the possible return values of a function.
  helper : forall {p1 c q1 cc cp2} 
           -> q1 ≡ conv-proc p1
           -> cc ≡ conv-act c
           -> ccs-Reduc {conv-penv} q1 cc cp2
           -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp-Reduc {penv} p1 c p2)
  helper {chan-send _ _ p1} {send _ _} refl refl chan = p1 , refl , chan-send
  helper {chan-recv _ f} {recv _ v} refl refl (indet chan) = f v , refl , chan-recv
  helper {chan-tau p1} {tau} refl refl chan = p1 , refl , chan-tau
  
  helper {par pl pr} {c} refl e2 (par-L r) with helper {pl} {c} refl e2 r
  ... | p' , refl , r' = par p' pr , refl , par-L r'
  
  helper {par pl pr} {c} refl e2 (par-R r) with helper {pr} {c} refl e2 r
  ... | p' , refl , r' = par pl p' , refl , par-R r'

  helper {par pl pr} {tau} refl refl (par-B {send _} r1 r2) with unconv-reduc {pl} r1 | unconv-reduc {pr} r2
  ... | pl' , refl , rl | pr' , refl , rr = par pl' pr' , refl , par-B rl rr
  helper {par pl pr} {tau} refl refl (par-B {recv _} r1 r2) with unconv-reduc {pl} r1 | unconv-reduc {pr} r2
  ... | pl' , refl , rl | pr' , refl , rr = par pl' pr' , refl , par-B rl rr
  helper {par pl pr} {tau} refl refl (par-B {tau} r1 r2) with unconv-reduc {pl} r1 | unconv-reduc {pr} r2
  ... | pl' , refl , rl | pr' , refl , rr = par pl' pr' , refl , par-B rl rr
  
  helper {indet f} {c} refl refl (indet {s = s} r) with unconv-reduc {f s} {c} r
  ... | p' , refl , r' = p' , refl , indet {s = s} r'
  
  helper {const n args} {c} refl refl (const r) with unconv-reduc {penv n args} r
  ... | p' , refl , r' = p' , refl , const r'
  
  helper {rename f p1} {c} refl refl r = rename-helper refl r
    where
    -- Prove some guarantees about composing functions on channel/reduction operation that Agda can't prove.
    unconv-map-eq : forall {cc c f} -> map-action (conv-rename f) cc ≡ conv-act c
                    -> ∃[ c' ] (cc ≡ conv-act c' × c ≡ map-act f c')
    unconv-map-eq {send (conv-c c v)} {send _ _} refl = send c v , refl , refl
    unconv-map-eq {recv (conv-c c v)} {recv _ _} refl = recv c v , refl , refl
    unconv-map-eq {tau} {tau} refl = tau , refl , refl
    -- Like `helper`, this function is only needed to introduce the additional `cc` variable.
    rename-helper : forall {f p1 c cc cp2} -> cc ≡ conv-act c
                    -> ccs-Reduc {conv-penv} (rename (conv-rename f) (conv-proc p1)) cc cp2
                    -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp-Reduc {penv} (rename f p1) c p2)
    rename-helper {f} {p1} e (rename r) with unconv-map-eq e
    ... | c' , refl , refl with unconv-reduc {p1} r
    ... | p' , refl , r' = rename f p' , refl , rename r'
  
  helper {hide f p1} {c} refl refl (hide {z = z} r) with unconv-reduc {p1} r
  ... | p' , refl , r' = hide f p' , refl , hide {z = unconv-z {f} {c} z} r'
    where
    -- This function is here only to give Agda a hint on which type we want to do unification.
    unconv-z : forall {f c} -> T (ccs.filter-act (conv-hide f) (conv-act c)) -> T (vp.filter-act f c)
    unconv-z {f} {send c _} _ with f c
    ... | true = tt
    unconv-z {f} {recv c _} _ with f c
    ... | true = tt
    unconv-z {f} {tau} _ = tt
  
  helper {if false p1} refl refl (indet {s = ()} r)
  helper {if true p1} refl refl r with unconv-reduc {p1} r
  ... | p' , refl , r' = p' , refl , if r'
 