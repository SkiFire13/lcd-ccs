open import Data.Bool
open import Data.Product
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Structures using (IsEquivalence)

import ccs.proc

module bisimilarity.strong {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs {C} {N} {penv}
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
p-to-q (∼-to-~ (bisimilar p q R x)) {p' = p'} r =
  let q' , r' , x' = R .p-to-q x r
  in q' , r' , ∼-to-~ (bisimilar p' q' R x')
q-to-p (∼-to-~ (bisimilar p q R x)) {p' = q'} r =
  let p' , r' , x' = R .q-to-p x r
  in p' , r' , ∼-to-~ (bisimilar q' p' R x')
-- Strong bisimilarity (coinductive) implies strong bisimilarity (defined with a relation)
~-to-∼ : forall {p q} -> p ~ q -> p ∼ q
~-to-∼ {p} {q} p~q = bisimilar p q bis p~q
  where
  bis : Bisimulation
  R (bis) = _~_
  p-to-q (bis) = p-to-q
  q-to-p (bis) = q-to-p

-- From now on everything will use the coinductive definition

reflexive : Reflexive _~_ -- forall {p q} -> p ~ p
p-to-q (reflexive {p}) {p' = p'} r = p' , r , reflexive
q-to-p (reflexive {p}) {p' = p'} r = p' , r , reflexive

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

  helper {par c1 c2} refl refl p~q = helper-par (cong {c1} p~q) (cong {c2} p~q) .p-to-q
    where
    helper-par : forall {pl pr ql qr} -> pl ~ ql -> pr ~ qr -> par pl pr ~ par ql qr
    q-to-p (helper-par pl~ql pr~qr) = p-to-q (helper-par (sym pl~ql) (sym pr~qr))
    p-to-q (helper-par pl~ql pr~qr) = helper-par-p-to-q pl~ql pr~qr
      where
      helper-par-p-to-q : forall {pl pr ql qr} -> pl ~ ql -> pr ~ qr
                          -> BisimulationProperty _~_ (par pl pr) (par ql qr)
      helper-par-p-to-q {qr = qr} pl~ql pr~qr (par-L {p' = p'} r) =
        let q' , r' , p'~q' = pl~ql .p-to-q r
        in par q' qr , par-L r' , helper-par p'~q' pr~qr
      helper-par-p-to-q {ql = ql} pl~ql pr~qr (par-R {p' = p'} r) =
        let q' , r' , p'~q' = pr~qr .p-to-q r
        in par ql q' , par-R r' , helper-par pl~ql p'~q'
      helper-par-p-to-q pl~ql pr~qr (par-B {a} {pl' = pl'} {pr' = pr'} rl rr) =
        let ql' , rl' , pl'~ql' = pl~ql .p-to-q rl
            qr' , rr' , pr'~qr' = pr~qr .p-to-q rr
        in par ql' qr' , par-B rl' rr' , helper-par pl'~ql' pr'~qr'

  helper {indet f} refl refl p~q (indet {s = s} r) =
    let q' , r' , p'~q' = (cong {f s} p~q) .p-to-q r
    in q' , indet {s = s} r' , p'~q'

  helper {const _} refl refl _ = reflexive .p-to-q

  helper {rename f c} refl refl p~q (rename {a} r) =
    let q' , r' , p'~q' = (cong {c} p~q) .p-to-q r
    in rename f q' , rename {a} r' , cong p'~q'

  helper {hide f c} refl refl p~q (hide {z = z} r) =
    let q' , r' , p'~q' = (cong {c} p~q) .p-to-q r
    in hide f q' , hide {z = z} r' , cong p'~q'

  helper {replace} refl refl p~q = p~q .p-to-q
