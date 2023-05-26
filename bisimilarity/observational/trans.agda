{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.observational.trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.context C N penv
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.congruence C N penv
open import bisimilarity.weak.properties C N penv using () renaming (reflexive to ≈-refl; trans to ≈-trans)
open import bisimilarity.weak.string C N penv

-- An observable (weak) transition
record _=[_]=>ₒ_ (p₁ : Proc) (a : Act) (p₄ : Proc) : Set₁ where
  constructor obs-t
  field
    {p₂ p₃} : Proc
    s₁ : p₁ -[tau]→* p₂
    t  : p₂ -[ a ]→ p₃
    s₂ : p₃ -[tau]→* p₄

trans→obs : ∀ {p a q} → (p -[ a ]→ q) → (p =[ a ]=>ₒ q)
trans→obs t = obs-t self t self

obs→weak : ∀ {p a q} → (p =[ a ]=>ₒ q) → (p =[ a ]⇒ q)
obs→weak (obs-t s₁ t s₂) = join (tau s₁) (trans→weak t) (tau s₂)

merge-weak-tau : ∀ {p₁ p₂ p₃ a} → (p₁ =[ a ]=>ₒ p₂) → (p₂ =[ tau ]⇒ p₃) → (p₁ =[ a ]=>ₒ p₃)
merge-weak-tau (obs-t s₁ t s₂) (tau s₃) = obs-t s₁ t (concat s₂ s₃)

merge-weak-tau' : ∀ {p₁ p₂ p₃ a} → (p₁ =[ tau ]=>ₒ p₂) → (p₂ =[ a ]⇒ p₃) → (p₁ =[ a ]=>ₒ p₃)
merge-weak-tau' (obs-t s₁ t s₂) (send s₃ t' s₄) = obs-t (concat s₁ (cons t (concat s₂ s₃))) t' s₄
merge-weak-tau' (obs-t s₁ t s₂) (recv s₃ t' s₄) = obs-t (concat s₁ (cons t (concat s₂ s₃))) t' s₄
merge-weak-tau' (obs-t s₁ t s₂) (tau s₃) = obs-t s₁ t (concat s₂ s₃)

-- Observational weak bisimilarity property
ObsBisBisimulationProperty : (Proc → Proc → Set₁) → Proc → Proc → Set₁
ObsBisBisimulationProperty _R_ p q = ∀ {a p'} → (p -[ a ]→ p') → ∃[ q' ] ((q =[ a ]=>ₒ q') × p' R q')

-- Observational congruence defined as weak bisimilarity but with a forced strong transition
record _≈ₒ_ (p : Proc) (q : Proc) : Set₁ where
  field
    p⇒q : ObsBisBisimulationProperty _≈_ p q
    q⇒p : ObsBisBisimulationProperty _≈_ q p
open _≈ₒ_ public
infixl 5 _≈ₒ_

-- Prove that ≈ₒ implies ≈, even though it is pretty obvious
≈ₒ→≈ : ∀ {p q} → p ≈ₒ q → p ≈ q
p⇒q (≈ₒ→≈ p≈ₒq) t =
  let q' , t' , p'≈q' = p≈ₒq .p⇒q t
  in q' , obs→weak t' , p'≈q'
q⇒p (≈ₒ→≈ p≈ₒq) t =
  let p' , t' , p'≈q' = p≈ₒq .q⇒p t
  in p' , obs→weak t' , p'≈q'

-- Prove that ≈ₒ is an equivalence
reflexive : ∀ {p} → p ≈ₒ p
p⇒q reflexive {p' = p'} t = p' , trans→obs t , ≈-refl
q⇒p reflexive {p' = p'} t = p' , trans→obs t , ≈-refl

sym : ∀ {p q} → p ≈ₒ q → q ≈ₒ p
p⇒q (sym p≈ₒq) = p≈ₒq .q⇒p
q⇒p (sym p≈ₒq) = p≈ₒq .p⇒q

trans : ∀ {p q s} → p ≈ₒ q → q ≈ₒ s → p ≈ₒ s
p⇒q (trans p≈ₒq q≈ₒs) t with p≈ₒq .p⇒q t
... | q' , obs-t self tq s , p'≈q' =
  let s' , ts , q''≈s' = q≈ₒs .p⇒q tq
      s'' , ts' , q'≈s'' = p⇒q-tau q''≈s' s
  in s'' , merge-weak-tau ts ts' , ≈-trans p'≈q' q'≈s''
... | q' , obs-t (cons tq s₁) tq' s₂ , p'≈q' =
  let s' , ts , q''≈s' = q≈ₒs .p⇒q tq
      s'' , ts' , q'≈s'' = p⇒q-weak q''≈s' (obs→weak (obs-t s₁ tq' s₂))
  in s'' , merge-weak-tau' ts ts' , ≈-trans p'≈q' q'≈s''
q⇒p (trans p≈ₒq q≈ₒs) = p⇒q (trans (sym q≈ₒs) (sym p≈ₒq))

-- Prove that ≈ₒ is a congruence
cong : Cong _≈ₒ_
p⇒q (cong {chan a C[]} p≈ₒq) chan = subst C[] _ , trans→obs chan , ≈ₒ→≈ (cong p≈ₒq)
p⇒q (cong {par-L C[] pc} p≈ₒq) (par-L t) =
  let q' , obs-t s₁ tq s₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t
  in par q' pc , obs-t (s-map par-L s₁) (par-L tq) (s-map par-L s₂) , par-respects-≈ p'≈q' ≈-refl
p⇒q (cong {par-L C[] pc} p≈ₒq) (par-R {p' = pc'} t) = 
  par (subst C[] _) pc' , trans→obs (par-R t) , par-respects-≈ (≈ₒ→≈ (cong {C[]} p≈ₒq)) ≈-refl
p⇒q (cong {par-L C[] pc} p≈ₒq) (par-B {pr' = pc'} t₁ t₂) =
  let q' , obs-t sq₁ tq sq₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t₁
  in par q' pc' , obs-t (s-map par-L sq₁) (par-B tq t₂) (s-map par-L sq₂), par-respects-≈ p'≈q' ≈-refl
p⇒q (cong {par-R pc C[]} p≈ₒq) (par-L {p' = pc'} t) =
  par pc' (subst C[] _) , trans→obs (par-L t) , par-respects-≈ ≈-refl (≈ₒ→≈ (cong {C[]} p≈ₒq))
p⇒q (cong {par-R pc C[]} p≈ₒq) (par-R t) =
  let q' , obs-t s₁ tq s₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t
  in par pc q' , obs-t (s-map par-R s₁) (par-R tq) (s-map par-R s₂) , par-respects-≈ ≈-refl p'≈q'
p⇒q (cong {par-R pc C[]} p≈ₒq) (par-B {pl' = pc'} t₁ t₂) =
  let q' , obs-t sq₁ tq sq₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t₂
  in par pc' q' , obs-t (s-map par-R sq₁) (par-B t₁ tq) (s-map par-R sq₂), par-respects-≈ ≈-refl p'≈q'
p⇒q (cong {indet C[] pc} p≈ₒq) (indet right t) = _ , trans→obs (indet right t) , ≈-refl
p⇒q (cong {indet C[] pc} p≈ₒq) (indet left t) with cong {C[]} p≈ₒq .p⇒q t
... | q' , obs-t self tq s₂ , p'≈q' = q' , obs-t self (indet left tq) s₂ , p'≈q'
... | q' , obs-t (cons ts s₁) tq s₂ , p'≈q' = q' , obs-t (cons (indet left ts) s₁) tq s₂ , p'≈q'
p⇒q (cong {rename f C[]} p≈ₒq) (rename t) =
  let q' , obs-t sq₁ tq sq₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t
  in rename f q' , obs-t (s-map rename sq₁) (rename tq) (s-map rename sq₂) , rename-respects-≈ p'≈q'
p⇒q (cong {hide f C[]} p≈ₒq) (hide z t) =
  let q' , obs-t s₁ tq s₂ , p'≈q' = cong {C[]} p≈ₒq .p⇒q t
  in hide f q' , obs-t (s-map (hide tt) s₁) (hide z tq) (s-map (hide tt) s₂) , hide-respects-≈ p'≈q'
p⇒q (cong {replace} p≈ₒq) = p≈ₒq .p⇒q
q⇒p (cong p≈ₒq) = cong (sym p≈ₒq) .p⇒q
