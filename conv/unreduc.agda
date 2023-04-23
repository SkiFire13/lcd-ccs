open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Unit
open import Data.Product

import ccs-vp.proc

module conv.unreduc {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open import conv.proc {C} {N} {X} {V} {n-fv}

open import ccs {Conv-C} {Conv-N} {conv-penv penv} as ccs
open import ccs-vp {C} {N} {X} {V} {n-fv} {penv} as vp

-- Prove that the converse of `conv-reduc` is not true, that is if there's
-- a reduction relation between two CCS processes then it's not guaranteed that
-- there's a reduction relation between CCS-VP processes that can be converted into them. 
NaiveUnconv : Set₁
NaiveUnconv = forall {p1 c p2} 
  -> ccs.Reduc (conv-proc p1) (conv-act c) (conv-proc p2)
  -> vp.Reduc p1 c p2

unconv-need-exists : ¬ NaiveUnconv
unconv-need-exists f with f {chan-tau vp.deadlock} {tau} {if true vp.deadlock} chan
... | ()

-- Prove the less-strong version of the previous (false) theorem, that is
-- if a CCS-VP process converted to CCS has a relation with another CCS process
-- then there exists a corresponding relation between the initial CCS-VP process
-- and some other CCS-VP process that can be converted in the initial second CCS process.
unconv-reduc : forall {p1 c cp2} 
               -> ccs.Reduc (conv-proc p1) (conv-act c) cp2
               -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp.Reduc p1 c p2)
unconv-reduc = helper refl refl
  where
  -- This helper is needed because Agda prefers plain variables when pattern matching rather
  -- the possible return values of a function.
  helper : forall {p1 c cp1 cc cp2} 
           -> cp1 ≡ conv-proc p1
           -> cc ≡ conv-act c
           -> ccs.Reduc cp1 cc cp2
           -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp.Reduc p1 c p2)
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
                    -> ccs.Reduc (rename (conv-rename f) (conv-proc p1)) cc cp2
                    -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp.Reduc (rename f p1) c p2)
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
 
