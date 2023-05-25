{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.weak.string (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.weak.base C N penv

-- (Half) the property of a weak string bisimulation
StringBisimulationProperty : (Proc → Proc → Set₁) → Proc → Proc → Set₁
StringBisimulationProperty R p q = ∀ {a p'} → (p =[ a ]⇒ p') → ∃[ q' ] ((q =[ a ]⇒ q') × R p' q')

-- Weak bisimilarity defined coinductively
record _≈ₛ_ (p : Proc) (q : Proc) : Set₁ where
  coinductive
  field
    p⇒q : StringBisimulationProperty _≈ₛ_ p q
    q⇒p : StringBisimulationProperty _≈ₛ_ q p
open _≈ₛ_ public
infixl 5 _≈ₛ_

-- Utilities to help prove the following implications
p⇒q-tau : ∀ {p q p'} → p ≈ q → (p -[tau]→* p') → ∃[ q' ] (q =[ tau ]⇒ q' × p' ≈ q')
p⇒q-tau {q = q} p≈q self = q , tau self , p≈q
p⇒q-tau {q = q} p≈q (cons t s') =
  let q1 , r1 , p'≈q1 = p≈q .p⇒q t
      q2 , r2 , p'≈q2 = p⇒q-tau p'≈q1 s'
  in q2 , join-tau r1 r2 , p'≈q2
p⇒q-split : ∀ {p1 p2 p3 p4 q a} → p1 ≈ q → (p1 -[tau]→* p2) → (p2 -[ a ]→ p3) → (p3 -[tau]→* p4)
              → ∃[ q' ] (q =[ a ]⇒ q' × p4 ≈ q')
p⇒q-split p≈q s1 t s2 =
  let q1 , r1 , p'≈q1 = p⇒q-tau p≈q s1
      q2 , r2 , p'≈q2 = p'≈q1 .p⇒q t
      q3 , r3 , p'≈q3 = p⇒q-tau p'≈q2 s2
  in q3 , join r1 r2 r3 , p'≈q3
p⇒q-weak : ∀ {p q a p'} → p ≈ q → (p =[ a ]⇒ p') → ∃[ q' ] ((q =[ a ]⇒ q') × p' ≈ q')
p⇒q-weak p≈q (send s1 t s2) = p⇒q-split p≈q s1 t s2
p⇒q-weak p≈q (recv s1 t s2) = p⇒q-split p≈q s1 t s2
p⇒q-weak p≈q (tau s) = p⇒q-tau p≈q s

-- Weak string bisimilarity implies weak bisimilarity
≈ₛ→≈ : ∀ {p q} → p ≈ₛ q → p ≈ q
p⇒q (≈ₛ→≈ p≈ₛq) t =
  let q' , t' , p'≈ₛq' = p≈ₛq .p⇒q (trans→weak t)
  in q' , t' , ≈ₛ→≈ p'≈ₛq'
q⇒p (≈ₛ→≈ p≈ₛq) t =
  let p' , t' , q'≈ₛp' = p≈ₛq .q⇒p (trans→weak t)
  in p' , t' , ≈ₛ→≈ q'≈ₛp'

-- Weak bisimilarity implies weak string bisimilarity
≈→≈ₛ : ∀ {p q} → p ≈ q → p ≈ₛ q
q⇒p (≈→≈ₛ p≈q) = p⇒q (≈→≈ₛ record { p⇒q = p≈q .q⇒p ; q⇒p = p≈q .p⇒q })
p⇒q (≈→≈ₛ p≈q) t = let q' , t' , p'≈q' = p⇒q-weak p≈q t in q' , t' , ≈→≈ₛ p'≈q'
