open import Data.Bool
open import Data.Product
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Structures using (IsEquivalence)

import ccs.proc

module bisimilarity.strong {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.context {C} {N} {penv}

-- Definition of a strong bisimulation
record Bisimulation : Set₂ where
  field
    R : Proc -> Proc -> Set₁
    p-to-q : forall {a p q p'} -> R p q -> Trans p a p' -> ∃[ q' ] (Trans q a q' × R p' q')
    q-to-p : forall {a p q q'} -> R p q -> Trans q a q' -> ∃[ p' ] (Trans p a p' × R p' q')
open Bisimulation

-- Definition of strong bisimilarity 
data _∼_ : Proc -> Proc -> Set₂ where
  bisimilar : (p : Proc) -> (q : Proc) -> (b : Bisimulation) -> b .R p q -> p ∼ q


-- Strong bisimilarity defined coinductively
record _~_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : forall {a p'} -> Trans p a p' -> ∃[ q' ] (Trans q a q' × p' ~ q')
    q-to-p : forall {a q'} -> Trans q a q' -> ∃[ p' ] (Trans p a p' × p' ~ q')
open _~_


-- Properties of strong bisimilarity

reflexive : Reflexive _~_ -- forall {p q} -> p ~ p
p-to-q (reflexive {p}) {p' = p'} t = p' , t , reflexive
q-to-p (reflexive {p}) {q' = q'} t = q' , t , reflexive

sym : Symmetric _~_ -- forall {p q} -> p ~ q -> q ~ p
p-to-q (sym {p} {q} p~q) t =
  let q' , t' , q'~p' = p~q .q-to-p t
  in q' , t' , sym q'~p'
q-to-p (sym {p} {q} p~q) t =
  let p' , t' , p'~q' = p~q .p-to-q t
  in p' , t' , sym p'~q'

trans : Transitive _~_ -- forall {p q s} -> p ~ q -> q ~ s -> p ~ s
p-to-q (trans {p} {q} {s} p~q q~s) tp =
  let q' , tq , p'~q' = p~q .p-to-q tp
      s' , ts , q'~s' = q~s .p-to-q tq
  in s' , ts , trans p'~q' q'~s'
q-to-p (trans {p} {q} {s} p~q q~s) ts =
  let q' , tq , q'~s' = q~s .q-to-p ts
      p' , tp , p'~q' = p~q .q-to-p tq
  in p' , tp , trans p'~q' q'~s'

-- Agda's equivalence class, just to assert that ~ is effectively an equivalence
isEquivalence : IsEquivalence _~_
IsEquivalence.refl (isEquivalence) = reflexive
IsEquivalence.sym (isEquivalence) = sym
IsEquivalence.trans (isEquivalence) = trans


-- Strong bisimilarity (defined with a relation) implies strong bisimilarity (coinductive)
∼-to-~ : forall {p q} -> p ∼ q -> p ~ q
p-to-q (∼-to-~ (bisimilar p q R x)) {p' = p'} t =
  let q' , t' , x' = R .p-to-q x t
  in q' , t' , ∼-to-~ (bisimilar p' q' R x')
q-to-p (∼-to-~ (bisimilar p q R x)) {q' = q'} t =
  let p' , t' , x' = R .q-to-p x t
  in p' , t' , ∼-to-~ (bisimilar p' q' R x')
-- Strong bisimilarity (coinductive) implies strong bisimilarity (defined with a relation)
~-to-∼ : forall {p q} -> p ~ q -> p ∼ q
~-to-∼ {p} {q} p~q = bisimilar p q bis p~q
  where
  bis : Bisimulation
  R (bis) = _~_
  p-to-q (bis) t = p-to-q t
  q-to-p (bis) t = q-to-p t

-- Prove that ~ is a congruence

cong-par : forall {pl pr ql qr} -> pl ~ ql -> pr ~ qr -> par pl pr ~ par ql qr
p-to-q (cong-par {qr = qr} pl~ql pr~qr) (par-L {p' = p'} t) =
  let q' , t' , p'~q' = pl~ql .p-to-q t
  in par q' qr , par-L t' , cong-par p'~q' pr~qr
q-to-p (cong-par {pr = pr} pl~ql pr~qr) (par-L {p' = q'} t) =
  let p' , t' , p'~q' = pl~ql .q-to-p t
  in par p' pr , par-L t' , cong-par p'~q' pr~qr
p-to-q (cong-par {ql = ql} pl~ql pr~qr) (par-R {p' = p'} t) =
  let q' , t' , p'~q' = pr~qr .p-to-q t
  in par ql q' , par-R t' , cong-par pl~ql p'~q'
q-to-p (cong-par {pl = pl} pl~ql pr~qr) (par-R {p' = q'} t) =
  let p' , t' , p'~q' = pr~qr .q-to-p t
  in par pl p' , par-R t' , cong-par pl~ql p'~q'
p-to-q (cong-par pl~ql pr~qr) (par-B {a} {pl' = pl'} {pr' = pr'} tl tr) =
  let ql' , tl' , pl'~ql' = pl~ql .p-to-q tl
      qr' , tr' , pr'~qr' = pr~qr .p-to-q tr
  in par ql' qr' , par-B tl' tr' , cong-par pl'~ql' pr'~qr'
q-to-p (cong-par pl~ql pr~qr) (par-B {a} {pl' = ql'} {pr' = qr'} tl tr) =
  let pl' , tl' , pl'~ql' = pl~ql .q-to-p tl
      pr' , tr' , pr'~qr' = pr~qr .q-to-p tr
  in par pl' pr' , par-B tl' tr' , cong-par pl'~ql' pr'~qr'

cong : forall {C[] p q} -> p ~ q -> subst C[] p ~ subst C[] q
cong p~q = helper refl refl p~q
  where
  -- Prove only one half of the bisimulation property, the other can be proved through symmetry
  helper : forall {C[] p q ps qs} -> ps ≡ subst C[] p -> qs ≡ subst C[] q -> p ~ q -> ps ~ qs

  p-to-q (helper {chan a C[]} {q = q} refl refl p~q) chan = subst C[] q , chan , cong p~q
  q-to-p (helper {chan a C[]} {p = p} refl refl p~q) chan = subst C[] p , chan , cong p~q

  helper {par _ _} refl refl p~q = cong-par (cong p~q) (cong p~q)

  p-to-q (helper {indet f} refl refl p~q) (indet {s = s} t) =
    let q' , t' , p'~q' = (cong {f s} p~q) .p-to-q t
    in q' , indet {s = s} t' , p'~q'
  q-to-p (helper {indet f} refl refl p~q) (indet {s = s} t) =
    let p' , t' , p'~q' = (cong {f s} p~q) .q-to-p t
    in p' , indet {s = s} t' , p'~q'

  helper {const _} refl refl _ = reflexive

  p-to-q (helper {rename f C[]} refl refl p~q) (rename {a = a} t) =
    let q' , t' , p'~q' = (cong {C[]} p~q) .p-to-q t
    in rename f q' , rename {a = a} t' , cong p'~q'
  q-to-p (helper {rename f C[]} refl refl p~q) (rename {a = a} t) =
    let p' , t' , p'~q' = (cong {C[]} p~q) .q-to-p t
    in rename f p' , rename {a = a} t' , cong p'~q'

  p-to-q (helper {hide f C[]} refl refl p~q) (hide {z = z} t) =
    let q' , t' , p'~q' = (cong {C[]} p~q) .p-to-q t
    in hide f q' , hide {z = z} t' , cong p'~q'
  q-to-p (helper {hide f C[]} refl refl p~q) (hide {z = z} t) =
    let p' , t' , p'~q' = (cong {C[]} p~q) .q-to-p t
    in hide f p' , hide {z = z} t' , cong p'~q'

  helper {replace} refl refl p~q = p~q
