open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Unit
open import Data.Product

import ccs-vp.proc

module conv.inv-reduc {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open import conv.proc {C} {N} {X} {V} {n-fv}

open import ccs {Conv-C} {Conv-N} {conv-penv penv} as ccs
open import ccs-vp {C} {N} {X} {V} {n-fv} {penv} as vp

-- Prove that the converse of `conv-reduc` is not true, that is if there's
-- a reduction relation between two CCS processes then it's not guaranteed that
-- there's a reduction relation between CCS-VP processes that can be converted into them. 
NaiveInvConv : Set₁
NaiveInvConv = forall {p1 c p2} 
              -> ccs.Reduc (conv-proc p1) (conv-act c) (conv-proc p2)
              -> vp.Reduc p1 c p2

inv-conv-need-exists : ¬ NaiveInvConv
inv-conv-need-exists f with f {chan-tau vp.deadlock} {tau} {if true vp.deadlock} chan
... | ()

-- Prove some guarantees about composing functions on channel/reduction operation that Agda can't prove.
inv-conv-map-rename-eq : forall {cc c f}
                       -> map-action (conv-rename f) cc ≡ conv-act c
                       -> ∃[ c' ] (cc ≡ conv-act c' × c ≡ map-act f c')
inv-conv-map-rename-eq {send (conv-c c v)} {send _ _} refl = send c v , refl , refl
inv-conv-map-rename-eq {recv (conv-c c v)} {recv _ _} refl = recv c v , refl , refl
inv-conv-map-rename-eq {tau} {tau} refl = tau , refl , refl

-- The inverse conversion for the condition when hiding channels
inv-conv-hide-z : forall {f c}
                -> T (ccs.filter-act (conv-hide f) (conv-act c))
                -> T (vp.filter-act f c)
inv-conv-hide-z {f} {send c _} _ with f c
... | true = tt
inv-conv-hide-z {f} {recv c _} _ with f c
... | true = tt
inv-conv-hide-z {f} {tau} _ = tt

-- Prove the less-strong version of the previous (false) theorem, that is
-- if a CCS-VP process converted to CCS has a relation with another CCS process
-- then there exists a corresponding relation between the initial CCS-VP process
-- and some other CCS-VP process that can be converted in the initial second CCS process.
inv-conv-reduc : forall {p1 c cp2} 
               -> ccs.Reduc (conv-proc p1) (conv-act c) cp2
               -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp.Reduc p1 c p2)
inv-conv-reduc = helper refl refl
  where
  -- This helper is needed because Agda prefers plain variables when pattern matching rather
  -- the possible return values of a function.
  helper : forall {p1 c cp1 cc cp2} 
           -> cp1 ≡ conv-proc p1
           -> cc ≡ conv-act c
           -> ccs.Reduc cp1 cc cp2
           -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp.Reduc p1 c p2)
  helper {chan-send _ _ p} {send _ _} refl refl chan = p , refl , chan-send
  helper {chan-recv _ f} {recv _ v} refl refl (indet chan) = f v , refl , chan-recv
  helper {chan-tau p} {tau} refl refl chan = p , refl , chan-tau
  
  helper {par pl pr} {c} refl eq (par-L rl) with helper {pl} {c} refl eq rl
  ... | pl' , refl , rl' = par pl' pr , refl , par-L rl'
  
  helper {par pl pr} {c} refl eq (par-R rr) with helper {pr} {c} refl eq rr
  ... | pr' , refl , rr' = par pl pr' , refl , par-R rr'

  helper {par pl pr} {tau} refl refl (par-B {send _} rl rr) with inv-conv-reduc {pl} rl | inv-conv-reduc {pr} rr
  ... | pl' , refl , rl' | pr' , refl , rr' = par pl' pr' , refl , par-B rl' rr'
  helper {par pl pr} {tau} refl refl (par-B {recv _} rl rr) with inv-conv-reduc {pl} rl | inv-conv-reduc {pr} rr
  ... | pl' , refl , rl' | pr' , refl , rr' = par pl' pr' , refl , par-B rl' rr'
  helper {par pl pr} {tau} refl refl (par-B {tau} rl rr) with inv-conv-reduc {pl} rl | inv-conv-reduc {pr} rr
  ... | pl' , refl , rl' | pr' , refl , rr' = par pl' pr' , refl , par-B rl' rr'
  
  helper {indet f} {c} refl refl (indet {s = s} r) with inv-conv-reduc {f s} {c} r
  ... | p' , refl , r' = p' , refl , indet {s = s} r'
  
  helper {const n args} {c} refl refl (const r) with inv-conv-reduc {penv n args} r
  ... | p' , refl , r' = p' , refl , const r'
  
  helper {rename f p} {c} refl e (rename r) with inv-conv-map-rename-eq e
  ... | _ , refl , refl with inv-conv-reduc {p} r
  ... | p' , refl , r' = rename f p' , refl , rename r'
  
  helper {hide f p} {c} refl refl (hide {z = z} r) with inv-conv-reduc {p} r
  ... | p' , refl , r' = hide f p' , refl , hide {z = inv-conv-hide-z {f} {c} z} r'

  helper {if false _} refl refl (indet {s = ()} r)
  helper {if true p} refl refl r with inv-conv-reduc {p} r
  ... | p' , refl , r' = p' , refl , if r'
