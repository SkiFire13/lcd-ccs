open import Data.Bool
open import Data.Product
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import ccs
import ccs.proc

module bisimilarity {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open ccs {C} {N} {penv}

BisimulationProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
BisimulationProperty R p q = (a : Act) -> (p' : Proc) -> Reduc p a p'
                             -> ∃[ q' ] (Reduc q a q' × R p' q')

record Bisimulation : Set₂ where
  field
    R : Proc -> Proc -> Set₁
    p-to-q : forall {p q} -> R p q -> BisimulationProperty R p q
    q-to-p : forall {p q} -> R p q -> BisimulationProperty R q p
open Bisimulation

data _∼_ : Proc -> Proc -> Set₂ where
  bisimilar : (p : Proc) -> (q : Proc) -> (b : Bisimulation) -> b .R p q -> p ∼ q

record _~_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : BisimulationProperty _~_ p q
    q-to-p : BisimulationProperty _~_ q p
open _~_

∼-to-~ : forall {p q} -> p ∼ q -> p ~ q
p-to-q (∼-to-~ (bisimilar p q R x)) a p' r =
  let q' , r' , x' = R .p-to-q {p} {q} x a p' r
  in q' , r' , ∼-to-~ (bisimilar p' q' R x')
q-to-p (∼-to-~ (bisimilar p q R x)) a q' r =
  let p' , r' , x' = R .q-to-p {p} {q} x a q' r
  in p' , r' , ∼-to-~ (bisimilar q' p' R x')

~-to-∼ : forall {p q} -> p ~ q -> p ∼ q
~-to-∼ {p} {q} p~q = bisimilar p q bis p~q
  where
  bis : Bisimulation
  R (bis) = _~_
  p-to-q (bis) = p-to-q
  q-to-p (bis) = q-to-p

~-Reflexive : Reflexive _~_
p-to-q (~-Reflexive {p}) _ p' r = p' , r , ~-Reflexive
q-to-p (~-Reflexive {p}) _ p' r = p' , r , ~-Reflexive

~-Symmetric : Symmetric _~_
p-to-q (~-Symmetric {p} {q} p~q) = p~q .q-to-p
q-to-p (~-Symmetric {p} {q} p~q) = p~q .p-to-q

~-Transitive : Transitive _~_
p-to-q (~-Transitive {p} {q} {s} p~q q~s) a p' rp =
  let q' , rq , p'~q' = p~q .p-to-q a p' rp
      s' , rs , q'~s' = q~s .p-to-q a q' rq
  in s' , rs , ~-Transitive p'~q' q'~s'
q-to-p (~-Transitive {p} {q} {s} p~q q~s) a s' rp =
  let q' , rq , s'~q' = q~s .q-to-p a s' rp
      p' , rp , q'~p' = p~q .q-to-p a q' rq
  in p' , rp , ~-Transitive s'~q' q'~p'

data Context : Set₁ where
  chan    : Act -> Context -> Context
  par     : Context -> Context -> Context
  indet   : {S : Set} -> (S -> Context) -> Context
  const   : N -> Context
  rename  : (C -> C) -> Context -> Context
  hide    : (C -> Bool) -> Context -> Context
  replace : Context

subst : Context -> Proc -> Proc
subst (chan a c) p = chan a (subst c p)
subst (par c1 c2) p = par (subst c1 p) (subst c2 p)
subst (indet f) p = indet (\ s -> subst (f s) p)
subst (const n) p = const n
subst (rename f c) p = rename f (subst c p)
subst (hide f c) p = hide f (subst c p)
subst replace p = p

~-cong : forall {c p q} -> p ~ q -> subst c p ~ subst c q
~-cong = helper refl refl
  where
  helper : forall {c p q ps qs} -> ps ≡ subst c p -> qs ≡ subst c q -> p ~ q -> ps ~ qs

  p-to-q (helper {chan a c} {p} {q} refl refl p~q) _ _ chan = subst c q , chan , ~-cong p~q
  q-to-p (helper {chan a c} {p} {q} refl refl p~q) _ _ chan = subst c p , chan , ~-Symmetric (~-cong p~q)

  helper {par c1 c2} {p} {q} refl refl p~q = helper-par (~-cong {c1} p~q) (~-cong {c2} p~q)
    where
    helper-par : forall {pl pr ql qr} -> pl ~ ql -> pr ~ qr -> par pl pr ~ par ql qr
    p-to-q (helper-par {qr = qr} pl~ql pr~qr) a _ (par-L {p' = p'} r) =
      let q' , r' , p'~q' = pl~ql .p-to-q a p' r
      in par q' qr , par-L r' , helper-par p'~q' pr~qr
    q-to-p (helper-par {pr = pr} pl~ql pr~qr) a _ (par-L {p' = q'} r) =
      let p' , r' , q'~p' = pl~ql .q-to-p a q' r
      in par p' pr , par-L r' , helper-par q'~p' (~-Symmetric pr~qr)

    p-to-q (helper-par {ql = ql} pl~ql pr~qr) a _ (par-R {p' = p'} r) =
      let q' , r' , p'~q' = pr~qr .p-to-q a p' r
      in par ql q' , par-R r' , helper-par pl~ql p'~q'
    q-to-p (helper-par {pl = pl} pl~ql pr~qr) a _ (par-R {p' = q'} r) =
      let p' , r' , q'~p' = pr~qr .q-to-p a q' r
      in par pl p' , par-R r' , helper-par (~-Symmetric pl~ql) q'~p'

    p-to-q (helper-par pl~ql pr~qr) _ _ (par-B {a} {pl' = pl'} {pr' = pr'} rl rr) =
      let ql' , rl' , pl'~ql' = pl~ql .p-to-q a pl' rl
          qr' , rr' , pr'~qr' = pr~qr .p-to-q (flip-act a) pr' rr
      in par ql' qr' , par-B rl' rr' , helper-par pl'~ql' pr'~qr'
    q-to-p (helper-par pl~ql pr~qr) _ _ (par-B {a} {pl' = ql'} {pr' = qr'} rl rr) =
      let pl' , rl' , ql'~pl' = pl~ql .q-to-p a ql' rl
          pr' , rr' , qr'~pr' = pr~qr .q-to-p (flip-act a) qr' rr
      in par pl' pr' , par-B rl' rr' , helper-par ql'~pl' qr'~pr'
  
  p-to-q (helper {indet f} {p} {q} refl refl p~q) a p' (indet {s = s} r) =
    let q' , r' , p'~q' = (~-cong {f s} p~q) .p-to-q a p' r
    in q' , indet {s = s} r' , p'~q'
  q-to-p (helper {indet f} {p} {q} refl refl p~q) a q' (indet {s = s} r) =
    let p' , r' , q'~p' = (~-cong {f s} p~q) .q-to-p a q' r
    in p' , indet {s = s} r' , q'~p'
  
  helper {const n} {p} {q} refl refl p~q = ~-Reflexive
  
  p-to-q (helper {rename f c} refl refl p~q) _ (rename .f p') (rename {a} r) =
    let q' , r' , p'~q' = (~-cong {c} p~q) .p-to-q a p' r
    in rename f q' , rename {a} r' , ~-cong p'~q'
  q-to-p (helper {rename f c} refl refl p~q) _ (rename .f q') (rename {a} r) =
    let p' , r' , q'~p' = (~-cong {c} p~q) .q-to-p a q' r
    in rename f p' , rename {a} r' , ~-cong q'~p'

  p-to-q (helper {hide f c} refl refl p~q) a (hide .f p') (hide {z = z} r) =
    let q' , r' , p'~q' = (~-cong {c} p~q) .p-to-q a p' r
    in hide f q' , hide {z = z} r' , ~-cong p'~q'
  q-to-p (helper {hide f c} refl refl p~q) a (hide .f q') (hide {z = z} r) =
    let p' , r' , q'~p' = (~-cong {c} p~q) .q-to-p a q' r
    in hide f p' , hide {z = z} r' , ~-cong q'~p'

  helper {replace} refl refl p~q = p~q
