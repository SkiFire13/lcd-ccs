open import Data.Bool
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Unit
open import Data.Product

import ccs-vp.proc

module conv.inv-trans {C N X V : Set} {n-fv : N → X → Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open import conv.proc {C} {N} {X} {V} {n-fv}

open import ccs.common {Conv-C} {Conv-N} {conv-penv penv} as ccs
open import ccs-vp.common {C} {N} {X} {V} {n-fv} {penv} as vp

-- Prove that the converse of `conv-trans` is not true, that is if there's
-- a transition relation between two CCS processes then it's not guaranteed that
-- there's a transition between CCS VP processes that can be converted into them. 
NaiveInvConv : Set₁
NaiveInvConv = ∀ {p1 a p2} 
              → ccs.Trans (conv-proc p1) (conv-act a) (conv-proc p2)
              → vp.Trans p1 a p2
inv-conv-need-exists : ¬ NaiveInvConv
inv-conv-need-exists f with () <- f {tau vp.deadlock} {tau} {if true vp.deadlock} chan

-- Prove some guarantees about composing functions on channel/transition operation that Agda can't prove.

inv-conv-act : ∀ {ca} → ∃[ a ] (ca ≡ conv-act a)
inv-conv-act {send (conv-c c v)} = send c v , refl
inv-conv-act {recv (conv-c c v)} = recv c v , refl
inv-conv-act {tau} = tau , refl

inv-flip-eq : ∀ {a} → ccs.flip-act (conv-act a) ≡ conv-act (vp.flip-act a)
inv-flip-eq {send _ _} = refl
inv-flip-eq {recv _ _} = refl
inv-flip-eq {tau} = refl

inv-rename-eq : ∀ {a a' f} → conv-act a ≡ ccs.map-act (conv-rename f) (conv-act a') → a ≡ vp.map-act f a'
inv-rename-eq {send _ _} {send _ _} refl = refl
inv-rename-eq {recv _ _} {recv _ _} refl = refl
inv-rename-eq {tau} {tau} refl = refl

inv-filter-eq : ∀ {f a} → ccs.filter-act (conv-hide f) (conv-act a) ≡ vp.filter-act f a
inv-filter-eq {f} {send c _} = refl
inv-filter-eq {f} {recv c _} = refl
inv-filter-eq {f} {tau} = refl

-- Prove the less-strong version of the previous (false) theorem, that is
-- if a CCS VP process converted to CCS has a relation with another CCS process
-- then there exists a corresponding relation between the initial CCS VP process
-- and some other CCS VP process that can be converted in the initial second CCS process.
inv-conv-trans' : ∀ {p1 a cp2} 
               → ccs.Trans (conv-proc p1) (conv-act a) cp2
               → ∃[ p2 ] (cp2 ≡ conv-proc p2 × vp.Trans p1 a p2)
inv-conv-trans' {p1} {a} t with {conv-proc p1} | {conv-act a} | inspect conv-proc p1 | inspect conv-act a
inv-conv-trans' {send _ _ p} {send _ _} chan | [ refl ] | [ refl ] = p , refl , send
inv-conv-trans' {recv _ f} {recv _ v} (indet chan) | [ refl ] | [ refl ] = f v , refl , recv
inv-conv-trans' {tau p} {tau} chan | [ refl ] | [ refl ] = p , refl , tau
inv-conv-trans' {par pl pr} (par-L tl) | [ refl ] | [ e2 ] with refl <- e2
  with pl' , refl , tl' <- inv-conv-trans' {pl} tl = par pl' pr , refl , par-L tl'
inv-conv-trans' {par pl pr} (par-R tr) | [ refl ] | [ e2 ] with refl <- e2
  with pr' , refl , tr' <- inv-conv-trans' {pr} tr = par pl pr' , refl , par-R tr'
inv-conv-trans' {par pl pr} {tau} (par-B {a = ca} tl tr) | [ refl ] | [ refl ]
  with a , refl <- inv-conv-act {ca}
  rewrite inv-flip-eq {a}
  with pl' , refl , tl' <- inv-conv-trans' {pl} tl
  with pr' , refl , tr' <- inv-conv-trans' {pr} tr
  = par pl' pr' , refl , par-B tl' tr'
inv-conv-trans' {indet f} {a} (indet {s = s} t) | [ refl ] | [ refl ]
  with p' , refl , t' <- inv-conv-trans' {f s} {a} t = p' , refl , indet {s = s} t'
inv-conv-trans' {const n args} (const t) | [ refl ] | [ refl ]
  with p' , refl , t' <- inv-conv-trans' {penv n args} t = p' , refl , const t'
inv-conv-trans' {rename f p} (rename {a = ca} t) | [ refl ] | [ e ]
  with a , refl <- inv-conv-act {ca}
  rewrite inv-rename-eq e
  with p' , refl , t' <- inv-conv-trans' {p} t
  = rename f p' , refl , rename t'
inv-conv-trans' {hide f p} {a} (hide {z = z} t) | [ refl ] | [ refl ]
  rewrite inv-filter-eq {f} {a}
  with p' , refl , t' <- inv-conv-trans' {p} t = hide f p' , refl , hide {z = z} t'
inv-conv-trans' {if false _} (indet {s = ()} _) | [ refl ] | [ refl ]
inv-conv-trans' {if true p} t | [ refl ] | [ refl ]
  with p' , refl , t' <- inv-conv-trans' {p} t = p' , refl , if t'
