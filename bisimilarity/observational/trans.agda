{-# OPTIONS --safe --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.observational.trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.context C N penv
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.congruence C N penv
open import bisimilarity.weak.properties C N penv using () renaming (reflexive to ≈-refl; trans to ≈-trans)
open import bisimilarity.weak.string C N penv

-- An "observable" weak transition
-- This is like a weak transition, but without allowing self τ transitions
record _=[_]⇒ₒ_ (p₁ : Proc) (a : Act) (p₄ : Proc) : Set₁ where
  constructor obs
  field
    {p₂ p₃} : Proc
    s₁ : p₁ -[τ]→* p₂
    t  : p₂ -[ a ]→ p₃
    s₂ : p₃ -[τ]→* p₄

-- Lemmas for conversions to/from observable weak transitions

strong→obs : ∀ {p a q} → (p -[ a ]→ q) → (p =[ a ]⇒ₒ q)
strong→obs t = obs self t self

obs→weak : ∀ {p a q} → (p =[ a ]⇒ₒ q) → (p =[ a ]⇒ q)
obs→weak (obs s₁ t s₂) = join-w (τ s₁) (strong→weak t) (τ s₂)

merge-weak-τ-l : ∀ {p₁ p₂ p₃ a} → (p₁ =[ τ ]⇒ₒ p₂) → (p₂ =[ a ]⇒ p₃) → (p₁ =[ a ]⇒ₒ p₃)
merge-weak-τ-l (obs s₁ t s₂) (send s₃ t' s₄) = obs (join-s s₁ (cons t (join-s s₂ s₃))) t' s₄
merge-weak-τ-l (obs s₁ t s₂) (recv s₃ t' s₄) = obs (join-s s₁ (cons t (join-s s₂ s₃))) t' s₄
merge-weak-τ-l (obs s₁ t s₂) (τ s₃)          = obs s₁ t (join-s s₂ s₃)

merge-weak-τ-r : ∀ {p₁ p₂ p₃ a} → (p₁ =[ a ]⇒ₒ p₂) → (p₂ =[ τ ]⇒ p₃) → (p₁ =[ a ]⇒ₒ p₃)
merge-weak-τ-r (obs s₁ t s₂) (τ s₃) = obs s₁ t (join-s s₂ s₃)

-- Observational congruence
record _≈ₒ_ (p : Proc) (q : Proc) : Set₁ where
  field
    p⇒q : ∀ {a p'} → (p -[ a ]→ p') → ∃[ q' ] (q =[ a ]⇒ₒ q' × p' ≈ q')
    q⇒p : ∀ {a q'} → (q -[ a ]→ q') → ∃[ p' ] (p =[ a ]⇒ₒ p' × q' ≈ p')
open _≈ₒ_ public
infixl 5 _≈ₒ_

-- Prove that ≈ₒ implies ≈
≈ₒ→≈ : ∀ {p q} → p ≈ₒ q → p ≈ q
p⇒q (≈ₒ→≈ p≈ₒq) t =
  let q' , t' , p'≈q' = p≈ₒq .p⇒q t
  in  q' , obs→weak t' , p'≈q'
q⇒p (≈ₒ→≈ p≈ₒq) t =
  let p' , t' , p'≈q' = p≈ₒq .q⇒p t
  in  p' , obs→weak t' , p'≈q'

-- Prove that ≈ₒ is an equivalence

reflexive : ∀ {p} → p ≈ₒ p
p⇒q reflexive t = _ , strong→obs t , ≈-refl
q⇒p reflexive t = _ , strong→obs t , ≈-refl

sym : ∀ {p q} → p ≈ₒ q → q ≈ₒ p
p⇒q (sym p≈ₒq) = p≈ₒq .q⇒p
q⇒p (sym p≈ₒq) = p≈ₒq .p⇒q

trans : ∀ {p q s} → p ≈ₒ q → q ≈ₒ s → p ≈ₒ s
p⇒q (trans p≈ₒq q≈ₒs) t with p≈ₒq .p⇒q t
... | q' , obs self tq s , p'≈q' =
  let s' , ts , q''≈s' = q≈ₒs .p⇒q tq
      s'' , ts' , q'≈s'' = p⇒q-τ q''≈s' s
  in  s'' , merge-weak-τ-r ts ts' , ≈-trans p'≈q' q'≈s''
... | q' , obs (cons tq s₁) tq' s₂ , p'≈q' =
  let s' , ts , q''≈s' = q≈ₒs .p⇒q tq
      s'' , ts' , q'≈s'' = p⇒q-weak q''≈s' (obs→weak (obs s₁ tq' s₂))
  in  s'' , merge-weak-τ-l ts ts' , ≈-trans p'≈q' q'≈s''
q⇒p (trans p≈ₒq q≈ₒs) = p⇒q (trans (sym q≈ₒs) (sym p≈ₒq))

-- Prove that ≈ₒ is a congruence
cong : Cong _≈ₒ_
p⇒q (cong {chan a C[]} {q = q} p≈ₒq) chan = subst C[] q , strong→obs chan , ≈ₒ→≈ (cong p≈ₒq)
p⇒q (cong {par C[] pc} p≈ₒq) (par-L t) =
  let q' , obs s₁ tq s₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t
  in  par q' pc , obs (map-s par-L s₁) (par-L tq) (map-s par-L s₂) , par-respects-≈ p'≈q' ≈-refl
p⇒q (cong {par C[] pc} {q = q} p≈ₒq) (par-R {p' = pc'} t) = 
  par (subst C[] q) pc' , strong→obs (par-R t) , par-respects-≈ (≈ₒ→≈ (cong {C[]} p≈ₒq)) ≈-refl
p⇒q (cong {par C[] pc} p≈ₒq) (par-B {pr' = pc'} t₁ t₂) =
  let q' , obs sq₁ tq sq₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t₁
  in  par q' pc' , obs (map-s par-L sq₁) (par-B tq t₂) (map-s par-L sq₂), par-respects-≈ p'≈q' ≈-refl
p⇒q (cong {indet C[] pc} p≈ₒq) {p' = pc'} (indet right t) = pc' , strong→obs (indet right t) , ≈-refl
p⇒q (cong {indet C[] pc} p≈ₒq) (indet left t) with cong {C[]} p≈ₒq .p⇒q t
... | q' , obs self tq s₂ , p'≈q' = q' , obs self (indet left tq) s₂ , p'≈q'
... | q' , obs (cons ts s₁) tq s₂ , p'≈q' = q' , obs (cons (indet left ts) s₁) tq s₂ , p'≈q'
p⇒q (cong {rename f C[]} p≈ₒq) (rename t) =
  let q' , obs sq₁ tq sq₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t
  in  rename f q' , obs (map-s rename sq₁) (rename tq) (map-s rename sq₂) , rename-respects-≈ p'≈q'
p⇒q (cong {hide f C[]} p≈ₒq) (hide z t) =
  let q' , obs s₁ tq s₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t
  in  hide f q' , obs (map-s (hide tt) s₁) (hide z tq) (map-s (hide tt) s₂) , hide-respects-≈ p'≈q'
p⇒q (cong {hole} p≈ₒq) = p≈ₒq .p⇒q
q⇒p (cong p≈ₒq) = cong (sym p≈ₒq) .p⇒q
