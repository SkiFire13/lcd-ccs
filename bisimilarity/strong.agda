open import Data.Bool
open import Data.Product
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Structures using (IsEquivalence)

import ccs.proc

module bisimilarity.strong {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.context {C} {N} {penv}

-- (Half) the property of a strong bisimulation
BisimulationProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
BisimulationProperty R p q = forall {a p'} -> Trans p a p' -> ∃[ q' ] (Trans q a q' × R p' q')

-- Definition of a strong bisimulation
record Bisimulation : Set₂ where
  field
    R : Proc -> Proc -> Set₁
    p-to-q : forall {p q} -> R p q -> BisimulationProperty R p q
    q-to-p : forall {p q} -> R p q -> BisimulationProperty R q p
open Bisimulation

-- Definition of strong bisimilarity 
data _∼_ : Proc -> Proc -> Set₂ where
  bisimilar : (p : Proc) -> (q : Proc) -> (b : Bisimulation) -> b .R p q -> p ∼ q

-- Strong bisimilarity defined coinductively
record _~_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : BisimulationProperty _~_ p q
    q-to-p : BisimulationProperty _~_ q p
open _~_

-- Strong bisimilarity (defined with a relation) implies strong bisimilarity (coinductive)
∼-to-~ : forall {p q} -> p ∼ q -> p ~ q
p-to-q (∼-to-~ (bisimilar p q R x)) {p' = p'} t =
  let q' , t' , x' = R .p-to-q x t
  in q' , t' , ∼-to-~ (bisimilar p' q' R x')
q-to-p (∼-to-~ (bisimilar p q R x)) {p' = q'} t =
  let p' , t' , x' = R .q-to-p x t
  in p' , t' , ∼-to-~ (bisimilar q' p' R x')
-- Strong bisimilarity (coinductive) implies strong bisimilarity (defined with a relation)
~-to-∼ : forall {p q} -> p ~ q -> p ∼ q
~-to-∼ {p} {q} p~q = bisimilar p q bis p~q
  where
  bis : Bisimulation
  R (bis) = _~_
  p-to-q (bis) = p-to-q
  q-to-p (bis) = q-to-p

-- From now on everything will use the coinductive definition


-- Properties of strong bisimilarity

reflexive : Reflexive _~_ -- forall {p q} -> p ~ p
p-to-q (reflexive {p}) {p' = p'} t = p' , t , reflexive
q-to-p (reflexive {p}) {p' = p'} t = p' , t , reflexive

sym : Symmetric _~_ -- forall {p q} -> p ~ q -> q ~ p
p-to-q (sym {p} {q} p~q) = p~q .q-to-p
q-to-p (sym {p} {q} p~q) = p~q .p-to-q

trans : Transitive _~_ -- forall {p q s} -> p ~ q -> q ~ s -> p ~ s
p-to-q (trans {p} {q} {s} p~q q~s) rp =
  let q' , rq , p'~q' = p~q .p-to-q rp
      s' , rs , q'~s' = q~s .p-to-q rq
  in s' , rs , trans p'~q' q'~s'
q-to-p (trans {p} {q} {s} p~q q~s) = p-to-q (trans (sym q~s) (sym p~q))

-- Agda's equivalence class, just to assert that ~ is effectively an equivalence
isEquivalence : IsEquivalence _~_
IsEquivalence.refl (isEquivalence) = reflexive
IsEquivalence.sym (isEquivalence) = sym
IsEquivalence.trans (isEquivalence) = trans

-- Prove that ~ is a congruence
cong : forall {c} -> Homomorphic₂ Proc Proc _~_ _~_ (subst c) -- forall {c p q} -> p ~ q -> subst c p ~ subst c q
q-to-p (cong p~q) = p-to-q (cong (sym p~q))
p-to-q (cong p~q) = helper refl refl p~q
  where
  -- Prove only one half of the bisimulation property, the other can be proved through symmetry
  helper : forall {c p q ps qs} -> ps ≡ subst c p -> qs ≡ subst c q -> p ~ q
           -> BisimulationProperty _~_ ps qs

  helper {chan a c} {q = q} refl refl p~q chan = subst c q , chan , cong p~q

  helper {par c1 c2} refl refl p~q = p-to-q (helper-par (cong {c1} p~q) (cong {c2} p~q))
    where
    helper-par : forall {pl pr ql qr} -> pl ~ ql -> pr ~ qr -> par pl pr ~ par ql qr
    q-to-p (helper-par pl~ql pr~qr) = p-to-q (helper-par (sym pl~ql) (sym pr~qr))
    p-to-q (helper-par {qr = qr} pl~ql pr~qr) (par-L {p' = p'} t) =
      let q' , t' , p'~q' = pl~ql .p-to-q t
      in par q' qr , par-L t' , helper-par p'~q' pr~qr
    p-to-q (helper-par {ql = ql} pl~ql pr~qr) (par-R {p' = p'} t) =
      let q' , t' , p'~q' = pr~qr .p-to-q t
      in par ql q' , par-R t' , helper-par pl~ql p'~q'
    p-to-q (helper-par pl~ql pr~qr) (par-B {a} {pl' = pl'} {pr' = pr'} tl tr) =
      let ql' , tl' , pl'~ql' = pl~ql .p-to-q tl
          qr' , tr' , pr'~qr' = pr~qr .p-to-q tr
      in par ql' qr' , par-B tl' tr' , helper-par pl'~ql' pr'~qr'

  helper {indet f} refl refl p~q (indet {s = s} t) =
    let q' , t' , p'~q' = (cong {f s} p~q) .p-to-q t
    in q' , indet {s = s} t' , p'~q'

  helper {const _} refl refl _ = reflexive .p-to-q

  helper {rename f c} refl refl p~q (rename {a = a} t) =
    let q' , t' , p'~q' = (cong {c} p~q) .p-to-q t
    in rename f q' , rename {a = a} t' , cong p'~q'

  helper {hide f c} refl refl p~q (hide {z = z} t) =
    let q' , t' , p'~q' = (cong {c} p~q) .p-to-q t
    in hide f q' , hide {z = z} t' , cong p'~q'

  helper {replace} refl refl p~q = p~q .p-to-q
