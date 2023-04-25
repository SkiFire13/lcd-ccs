open import Data.Bool
open import Data.Product
open import Relation.Binary.Definitions using (Reflexive; Symmetric; Transitive)
open import Relation.Binary.Morphism.Definitions using (Homomorphic₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Binary.Structures using (IsEquivalence)
open import Relation.Nullary

import ccs.proc

module bisimilarity.weak {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv} as ctx

-- (Half) the property of a weak bisimulation
BisimulationProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
BisimulationProperty R p q = forall {a p'} -> Trans p a p' -> ∃[ q' ] (WeakTrans q a q' × R p' q')

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
p-to-q (≈ᵣ-to-≈ (bisimilar p q R x)) {p' = p'} t =
  let q' , t' , x' = R .p-to-q {p} {q} x t
  in q' , t' , ≈ᵣ-to-≈ (bisimilar p' q' R x')
q-to-p (≈ᵣ-to-≈ (bisimilar p q R x)) {p' = q'} t =
  let p' , t' , x' = R .q-to-p {p} {q} x t
  in p' , t' , ≈ᵣ-to-≈ (bisimilar q' p' R x')
-- Weak bisimilarity (coinductive) implies weak bisimilarity (defined with a relation)
≈-to-≈ᵣ : forall {p q} -> p ≈ q -> p ≈ᵣ q
≈-to-≈ᵣ {p} {q} p≈q = bisimilar p q bis p≈q
  where
  bis : Bisimulation
  R (bis) = _≈_
  p-to-q (bis) = p-to-q
  q-to-p (bis) = q-to-p

-- From now on everything will use the coinductive definition


-- (Half) the property of a weak string bisimulation
StringBisimulationProperty : (Proc -> Proc -> Set₁) -> Proc -> Proc -> Set₁
StringBisimulationProperty R p q = forall {a p'} -> WeakTrans p a p' -> ∃[ q' ] (WeakTrans q a q' × R p' q')

-- Weak bisimilarity defined coinductively
record _≈ₛ_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p-to-q : StringBisimulationProperty _≈ₛ_ p q
    q-to-p : StringBisimulationProperty _≈ₛ_ q p
open _≈ₛ_

-- Weak string bisimilarity implies weak bisimilarity
≈ₛ-to-≈ : forall {p q} -> p ≈ₛ q -> p ≈ q
p-to-q (≈ₛ-to-≈ p≈ₛq) t =
  let q' , t' , p'≈ₛq' = p≈ₛq .p-to-q (trans-to-weak t)
  in q' , t' , ≈ₛ-to-≈ p'≈ₛq'
q-to-p (≈ₛ-to-≈ p≈ₛq) t =
  let p' , t' , q'≈ₛp' = p≈ₛq .q-to-p (trans-to-weak t)
  in p' , t' , ≈ₛ-to-≈ q'≈ₛp'
-- Weak bisimilarity implies weak string bisimilarity
≈-to-≈ₛ : forall {p q} -> p ≈ q -> p ≈ₛ q
q-to-p (≈-to-≈ₛ p≈q) = p-to-q (≈-to-≈ₛ record { p-to-q = p≈q .q-to-p ; q-to-p = p≈q .p-to-q })
p-to-q (≈-to-≈ₛ p≈q) t =
  let q' , t' , p'≈q' = p-to-q-weak p≈q t
  in q' , t' , ≈-to-≈ₛ p'≈q'
  where
  p-to-q-tau : forall {p q p'} -> p ≈ q -> TauSeq p p' -> ∃[ q' ] (WeakTrans q tau q' × p' ≈ q')
  p-to-q-tau {q = q} p≈q self = q , tau self , p≈q
  p-to-q-tau {q = q} p≈q (cons t s') =
    let q1 , r1 , p'≈q1 = p≈q .p-to-q t
        q2 , r2 , p'≈q2 = p-to-q-tau p'≈q1 s'
    in q2 , join-tau r1 r2 , p'≈q2
  p-to-q-weak : forall {p q a p'} -> p ≈ q -> WeakTrans p a p' -> ∃[ q' ] (WeakTrans q a q' × p' ≈ q')
  p-to-q-weak p≈q (send s1 t s2) =
    let q1 , r1 , p'≈q1 = p-to-q-tau p≈q s1
        q2 , r2 , p'≈q2 = p'≈q1 .p-to-q t
        q3 , r3 , p'≈q3 = p-to-q-tau p'≈q2 s2
    in q3 , join r1 r2 r3 , p'≈q3
  p-to-q-weak p≈q (recv s1 t s2) =
    let q1 , r1 , p'≈q1 = p-to-q-tau p≈q s1
        q2 , r2 , p'≈q2 = p'≈q1 .p-to-q t
        q3 , r3 , p'≈q3 = p-to-q-tau p'≈q2 s2
    in q3 , join r1 r2 r3 , p'≈q3
  p-to-q-weak p≈q (tau s) = p-to-q-tau p≈q s

-- Properties of weak bisimilarity

reflexive : Reflexive _≈_ -- forall {p q} -> p ≈ p
p-to-q (reflexive {p}) {p' = p'} t = p' , trans-to-weak t , reflexive
q-to-p (reflexive {p}) {p' = p'} t = p' , trans-to-weak t , reflexive

sym : Symmetric _≈_ -- forall {p q} -> p ≈ q -> q ≈ p
p-to-q (sym {p} {q} p≈q) = p≈q .q-to-p
q-to-p (sym {p} {q} p≈q) = p≈q .p-to-q

trans : Transitive _≈_ -- forall {p q s} -> p ≈ q -> q ≈ s -> p ≈ s
p-to-q (trans {p} {q} {s} p≈q q≈s) rp =
  let q' , rq , p'≈q' = p≈q .p-to-q rp
      s' , rs , q'≈ₛs' = ≈-to-≈ₛ q≈s .p-to-q rq
      q'≈s' = ≈ₛ-to-≈ q'≈ₛs'
  in s' , rs , trans p'≈q' q'≈s'
q-to-p (trans {p} {q} {s} p≈q q≈s) = p-to-q (trans (sym q≈s) (sym p≈q))

-- Agda's equivalence class, just to assert that ≈ is effectively an equivalence
isEquivalence : IsEquivalence _≈_
IsEquivalence.refl (isEquivalence) = reflexive
IsEquivalence.sym (isEquivalence) = sym
IsEquivalence.trans (isEquivalence) = trans

-- Prove that ≈ is not a congruence
-- forall {c} -> ¬ (forall {C[] p q} -> p ≈ q -> subst C[] p ≈ subst C[] q)
≈-not-cong : {c : C} -> ¬ forall {C[]} -> Homomorphic₂ Proc Proc _≈_ _≈_ (subst C[])
≈-not-cong {c} cong with cong {C[]} τd≈d .p-to-q (Trans.indet {s = true} chan)
  where
  τd≈d : chan tau ccs.deadlock ≈ ccs.deadlock
  p-to-q τd≈d (chan {p = q'}) = q' , tau self , reflexive
  q-to-p τd≈d (indet {s = ()} t)
  C[] = indet \ b -> if b then replace else chan (send c) ctx.deadlock
... | _ , tau (cons (indet {s = true} (indet {s = ()} _)) _) , _
... | _ , tau self , d≈c[d] with d≈c[d] .q-to-p (Trans.indet {s = false} chan)
...   | _ , send self (indet {s = ()} _) _ , _
...   | _ , send (cons (indet {s = ()} _) _) _ _ , _
