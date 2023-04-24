open import Data.Bool
open import Data.Product
open import Relation.Binary.Definitions
open import Relation.Binary.Morphism.Definitions
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Structures

import ccs.proc

module bisimilarity.weak {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs {C} {N} {penv}

-- (Half) the property of a weak bisimulation
BisimulationProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
BisimulationProperty R p q = forall {a p'} -> Reduc p a p' -> ∃[ q' ] (WeakReduc q a q' × R p' q')

-- Definition of a weak bisimulation
record Bisimulation : Set₂ where
  field
    R : Proc -> Proc -> Set₁
    p-to-q : forall {p q} -> R p q -> BisimulationProperty R p q
    q-to-p : forall {p q} -> R p q -> BisimulationProperty R q p
open Bisimulation

-- Definition of weak bisimilarity 
data _≈ᵣ_ : Proc -> Proc -> Set₂ where
  bisimilar : (p : Proc) -> (q : Proc) -> (b : Bisimulation) -> b .R p q -> p ≈ᵣ q

-- Weak bisimilarity defined coinductively
record _≈_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : BisimulationProperty _≈_ p q
    q-to-p : BisimulationProperty _≈_ q p
open _≈_

-- Weak bisimilarity (defined with a relation) implies weak bisimilarity (coinductive)
≈ᵣ-to-≈ : forall {p q} -> p ≈ᵣ q -> p ≈ q
p-to-q (≈ᵣ-to-≈ (bisimilar p q R x)) {p' = p'} r =
  let q' , r' , x' = R .p-to-q {p} {q} x r
  in q' , r' , ≈ᵣ-to-≈ (bisimilar p' q' R x')
q-to-p (≈ᵣ-to-≈ (bisimilar p q R x)) {p' = q'} r =
  let p' , r' , x' = R .q-to-p {p} {q} x r
  in p' , r' , ≈ᵣ-to-≈ (bisimilar q' p' R x')
-- Weak bisimilarity (coinductive) implies weak bisimilarity (defined with a relation)
≈-to-≈ᵣ : forall {p q} -> p ≈ q -> p ≈ᵣ q
≈-to-≈ᵣ {p} {q} p≈q = bisimilar p q bis p≈q
  where
  bis : Bisimulation
  R (bis) = _≈_
  p-to-q (bis) = p-to-q
  q-to-p (bis) = q-to-p

-- From now on everything will use the coinductive definition

-- Utils to prove transitivity
p-to-q-tau : forall {p q p'} -> p ≈ q -> TauSeq p p' -> ∃[ q' ] (WeakReduc q tau q' × p' ≈ q')
p-to-q-tau {q = q} p≈q self = q , tau self , p≈q
p-to-q-tau {q = q} p≈q (cons r s') =
  let q1 , r1 , p'≈q1 = p≈q .p-to-q r
      q2 , r2 , p'≈q2 = p-to-q-tau p'≈q1 s'
  in q2 , join-tau r1 r2 , p'≈q2
p-to-q-weak : forall {p q} -> p ≈ q
              -> forall {a p'} -> WeakReduc p a p'
              -> ∃[ q' ] (WeakReduc q a q' × p' ≈ q')
p-to-q-weak p≈q (send s1 r s2) =
  let q1 , r1 , p'≈q1 = p-to-q-tau p≈q s1
      q2 , r2 , p'≈q2 = p'≈q1 .p-to-q r
      q3 , r3 , p'≈q3 = p-to-q-tau p'≈q2 s2
  in q3 , join r1 r2 r3 , p'≈q3
p-to-q-weak p≈q (recv s1 r s2) =
  let q1 , r1 , p'≈q1 = p-to-q-tau p≈q s1
      q2 , r2 , p'≈q2 = p'≈q1 .p-to-q r
      q3 , r3 , p'≈q3 = p-to-q-tau p'≈q2 s2
  in q3 , join r1 r2 r3 , p'≈q3
p-to-q-weak p≈q (tau s) = p-to-q-tau p≈q s

reflexive : Reflexive _≈_ -- forall {p q} -> p ≈ p
p-to-q (reflexive {p}) {p' = p'} r = p' , reduc-to-weak r , reflexive
q-to-p (reflexive {p}) {p' = p'} r = p' , reduc-to-weak r , reflexive

sym : Symmetric _≈_ -- forall {p q} -> p ≈ q -> q ≈ p
p-to-q (sym {p} {q} p≈q) = p≈q .q-to-p
q-to-p (sym {p} {q} p≈q) = p≈q .p-to-q

trans : Transitive _≈_ -- forall {p q s} -> p ≈ q -> q ≈ s -> p ≈ s
p-to-q (trans {p} {q} {s} p≈q q≈s) rp =
  let q' , rq , p'≈q' = p≈q .p-to-q rp
      s' , rs , q'≈s' = p-to-q-weak q≈s rq
  in s' , rs , trans p'≈q' q'≈s'
q-to-p (trans {p} {q} {s} p≈q q≈s) = p-to-q (trans (sym q≈s) (sym p≈q))

-- Agda's equivalence class, just to assert that ≈ is effectively an equivalence
isEquivalence : IsEquivalence _≈_
IsEquivalence.refl (isEquivalence) = reflexive
IsEquivalence.sym (isEquivalence) = sym
IsEquivalence.trans (isEquivalence) = trans
