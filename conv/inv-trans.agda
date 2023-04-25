open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Unit
open import Data.Product

import ccs-vp.proc

module conv.inv-trans {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open import conv.proc {C} {N} {X} {V} {n-fv}

open import ccs.common {Conv-C} {Conv-N} {conv-penv penv} as ccs
open import ccs-vp.common {C} {N} {X} {V} {n-fv} {penv} as vp

-- Prove that the converse of `conv-trans` is not true, that is if there's
-- a transition relation between two CCS processes then it's not guaranteed that
-- there's a transition between CCS VP processes that can be converted into them. 
NaiveInvConv : Set₁
NaiveInvConv = forall {p1 a p2} 
              -> ccs.Trans (conv-proc p1) (conv-act a) (conv-proc p2)
              -> vp.Trans p1 a p2

inv-conv-need-exists : ¬ NaiveInvConv
inv-conv-need-exists f with f {tau vp.deadlock} {tau} {if true vp.deadlock} chan
... | ()

-- Prove some guarantees about composing functions on channel/transition operation that Agda can't prove.
inv-conv-map-rename-eq : forall {ca a f}
                       -> map-action (conv-rename f) ca ≡ conv-act a
                       -> ∃[ a' ] (ca ≡ conv-act a' × a ≡ map-act f a')
inv-conv-map-rename-eq {send (conv-c c v)} {send _ _} refl = send c v , refl , refl
inv-conv-map-rename-eq {recv (conv-c c v)} {recv _ _} refl = recv c v , refl , refl
inv-conv-map-rename-eq {tau} {tau} refl = tau , refl , refl

-- The inverse conversion for the condition when hiding channels
inv-conv-hide-z : forall {f a}
                -> T (ccs.filter-act (conv-hide f) (conv-act a))
                -> T (vp.filter-act f a)
inv-conv-hide-z {f} {send c _} _ with f c
... | true = tt
inv-conv-hide-z {f} {recv c _} _ with f c
... | true = tt
inv-conv-hide-z {f} {tau} _ = tt

-- Prove the less-strong version of the previous (false) theorem, that is
-- if a CCS VP process converted to CCS has a relation with another CCS process
-- then there exists a corresponding relation between the initial CCS VP process
-- and some other CCS VP process that can be converted in the initial second CCS process.
inv-conv-trans : forall {p1 a cp2} 
               -> ccs.Trans (conv-proc p1) (conv-act a) cp2
               -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp.Trans p1 a p2)
inv-conv-trans = helper refl refl
  where
  -- This helper is needed because Agda prefers plain variables when pattern matching rather
  -- the possible return values of a function.
  helper : forall {p1 a cp1 ca cp2} 
           -> cp1 ≡ conv-proc p1
           -> ca ≡ conv-act a
           -> ccs.Trans cp1 ca cp2
           -> ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp.Trans p1 a p2)
  helper {send _ _ p} {send _ _} refl refl chan = p , refl , send
  helper {recv _ f} {recv _ v} refl refl (indet chan) = f v , refl , recv
  helper {tau p} {tau} refl refl chan = p , refl , tau
  
  helper {par pl pr} refl eq (par-L tl) with helper {pl} refl eq tl
  ... | pl' , refl , tl' = par pl' pr , refl , par-L tl'
  
  helper {par pl pr} refl eq (par-R tr) with helper {pr} refl eq tr
  ... | pr' , refl , tr' = par pl pr' , refl , par-R tr'

  helper {par pl pr} {tau} refl refl (par-B {a = send _} tl tr) with inv-conv-trans {pl} tl | inv-conv-trans {pr} tr
  ... | pl' , refl , tl' | pr' , refl , tr' = par pl' pr' , refl , par-B tl' tr'
  helper {par pl pr} {tau} refl refl (par-B {a = recv _} tl tr) with inv-conv-trans {pl} tl | inv-conv-trans {pr} tr
  ... | pl' , refl , tl' | pr' , refl , tr' = par pl' pr' , refl , par-B tl' tr'
  helper {par pl pr} {tau} refl refl (par-B {a = tau} tl tr) with inv-conv-trans {pl} tl | inv-conv-trans {pr} tr
  ... | pl' , refl , tl' | pr' , refl , tr' = par pl' pr' , refl , par-B tl' tr'
  
  helper {indet f} {a} refl refl (indet {s = s} t) with inv-conv-trans {f s} {a} t
  ... | p' , refl , t' = p' , refl , indet {s = s} t'
  
  helper {const n args} refl refl (const t) with inv-conv-trans {penv n args} t
  ... | p' , refl , t' = p' , refl , const t'
  
  helper {rename f p} refl e (rename t) with inv-conv-map-rename-eq e
  ... | _ , refl , refl with inv-conv-trans {p} t
  ... | p' , refl , t' = rename f p' , refl , rename t'
  
  helper {hide f p} {a} refl refl (hide {z = z} t) with inv-conv-trans {p} t
  ... | p' , refl , t' = hide f p' , refl , hide {z = inv-conv-hide-z {f} {a} z} t'

  helper {if false _} refl refl (indet {s = ()} t)
  helper {if true p} refl refl t with inv-conv-trans {p} t
  ... | p' , refl , t' = p' , refl , if t'
