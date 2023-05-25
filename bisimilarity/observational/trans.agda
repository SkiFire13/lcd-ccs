{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product

import ccs.proc

module bisimilarity.observational.trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.cong C N penv
open import bisimilarity.context C N penv
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.congruence C N penv
open import bisimilarity.weak.properties C N penv using () renaming (reflexive to ≈-refl; trans to ≈-trans)
open import bisimilarity.weak.string C N penv

-- An observable (weak) transition
record _=[_]=>ₒ_ (p1 : Proc) (a : Act) (p4 : Proc) : Set₁ where
  constructor obs-t
  field
    {p2 p3} : Proc
    s1 : p1 -[tau]→* p2
    t  : p2 -[ a ]→ p3
    s2 : p3 -[tau]→* p4

trans-to-obs : ∀ {p a q} → (p -[ a ]→ q) → (p =[ a ]=>ₒ q)
trans-to-obs t = obs-t self t self

obs-to-weak : ∀ {p a q} → (p =[ a ]=>ₒ q) → (p =[ a ]⇒ q)
obs-to-weak (obs-t s1 t s2) = join (tau s1) (trans-to-weak t) (tau s2)

merge-weak-tau : ∀ {p1 p2 p3 a} → (p1 =[ a ]=>ₒ p2) → (p2 =[ tau ]⇒ p3) → (p1 =[ a ]=>ₒ p3)
merge-weak-tau (obs-t s1 t s2) (tau s3) = obs-t s1 t (concat s2 s3)

merge-weak-tau' : ∀ {p1 p2 p3 a} → (p1 =[ tau ]=>ₒ p2) → (p2 =[ a ]⇒ p3) → (p1 =[ a ]=>ₒ p3)
merge-weak-tau' (obs-t s1 t s2) (send s3 t' s4) = obs-t (concat s1 (cons t (concat s2 s3))) t' s4
merge-weak-tau' (obs-t s1 t s2) (recv s3 t' s4) = obs-t (concat s1 (cons t (concat s2 s3))) t' s4
merge-weak-tau' (obs-t s1 t s2) (tau s3) = obs-t s1 t (concat s2 s3)

-- Observational weak bisimilarity property
ObsBisProperty : (Proc → Proc → Set₁) → Proc → Proc → Set₁
ObsBisProperty R p q = ∀ {a p'} → (p -[ a ]→ p') → ∃[ q' ] ((q =[ a ]=>ₒ q') × R p' q')

-- Observational congruence defined as weak bisimilarity but with a forced strong transition
record _≈ₒ_ (p : Proc) (q : Proc) : Set₁ where
  field
    p-to-q : ObsBisProperty _≈_ p q
    q-to-p : ObsBisProperty _≈_ q p
open _≈ₒ_ public
infixl 5 _≈ₒ_

-- Prove that ≈ₒ implies ≈, even though it is pretty obvious
≈ₒ-to-≈ : ∀ {p q} → p ≈ₒ q → p ≈ q
p-to-q (≈ₒ-to-≈ p≈ₒq) t =
  let q' , t' , p'≈q' = p≈ₒq .p-to-q t
  in q' , obs-to-weak t' , p'≈q'
q-to-p (≈ₒ-to-≈ p≈ₒq) t =
  let p' , t' , p'≈q' = p≈ₒq .q-to-p t
  in p' , obs-to-weak t' , p'≈q'

-- Prove that ≈ₒ is an equivalence
reflexive : ∀ {p} → p ≈ₒ p
p-to-q reflexive {p' = p'} t = p' , trans-to-obs t , ≈-refl
q-to-p reflexive {p' = p'} t = p' , trans-to-obs t , ≈-refl

sym : ∀ {p q} → p ≈ₒ q → q ≈ₒ p
p-to-q (sym p≈ₒq) = p≈ₒq .q-to-p
q-to-p (sym p≈ₒq) = p≈ₒq .p-to-q

trans : ∀ {p q s} → p ≈ₒ q → q ≈ₒ s → p ≈ₒ s
p-to-q (trans p≈ₒq q≈ₒs) t with p≈ₒq .p-to-q t
... | q' , obs-t self tq s , p'≈q' =
  let s' , ts , q''≈s' = q≈ₒs .p-to-q tq
      s'' , ts' , q'≈s'' = p-to-q-tau q''≈s' s
  in s'' , merge-weak-tau ts ts' , ≈-trans p'≈q' q'≈s''
... | q' , obs-t (cons tq s1) tq' s2 , p'≈q' =
  let s' , ts , q''≈s' = q≈ₒs .p-to-q tq
      s'' , ts' , q'≈s'' = p-to-q-weak q''≈s' (obs-to-weak (obs-t s1 tq' s2))
  in s'' , merge-weak-tau' ts ts' , ≈-trans p'≈q' q'≈s''
q-to-p (trans p≈ₒq q≈ₒs) = p-to-q (trans (sym q≈ₒs) (sym p≈ₒq))

-- Prove that ≈ₒ is a congruence
cong : Cong _≈ₒ_
p-to-q (cong {chan a C[]} p≈ₒq) chan = subst C[] _ , trans-to-obs chan , ≈ₒ-to-≈ (cong p≈ₒq)
p-to-q (cong {par-L C[] pc} p≈ₒq) (par-L t) =
  let q' , obs-t s1 tq s2 , p'≈q' = cong {C[]} p≈ₒq .p-to-q t
  in par q' pc , obs-t (s-map par-L s1) (par-L tq) (s-map par-L s2) , par-respects-≈ p'≈q' ≈-refl
p-to-q (cong {par-L C[] pc} p≈ₒq) (par-R {p' = pc'} t) = 
  par (subst C[] _) pc' , trans-to-obs (par-R t) , par-respects-≈ (≈ₒ-to-≈ (cong {C[]} p≈ₒq)) ≈-refl
p-to-q (cong {par-L C[] pc} p≈ₒq) (par-B {pr' = pc'} t1 t2) =
  let q' , obs-t sq1 tq sq2 , p'≈q' = cong {C[]} p≈ₒq .p-to-q t1
  in par q' pc' , obs-t (s-map par-L sq1) (par-B tq t2) (s-map par-L sq2), par-respects-≈ p'≈q' ≈-refl
p-to-q (cong {par-R pc C[]} p≈ₒq) (par-L {p' = pc'} t) =
  par pc' (subst C[] _) , trans-to-obs (par-L t) , par-respects-≈ ≈-refl (≈ₒ-to-≈ (cong {C[]} p≈ₒq))
p-to-q (cong {par-R pc C[]} p≈ₒq) (par-R t) =
  let q' , obs-t s1 tq s2 , p'≈q' = cong {C[]} p≈ₒq .p-to-q t
  in par pc q' , obs-t (s-map par-R s1) (par-R tq) (s-map par-R s2) , par-respects-≈ ≈-refl p'≈q'
p-to-q (cong {par-R pc C[]} p≈ₒq) (par-B {pl' = pc'} t1 t2) =
  let q' , obs-t sq1 tq sq2 , p'≈q' = cong {C[]} p≈ₒq .p-to-q t2
  in par pc' q' , obs-t (s-map par-R sq1) (par-B t1 tq) (s-map par-R sq2), par-respects-≈ ≈-refl p'≈q'
p-to-q (cong {indet C[] pc} p≈ₒq) (indet {s = false} t) = _ , trans-to-obs (indet {s = false} t) , ≈-refl
p-to-q (cong {indet C[] pc} p≈ₒq) (indet {s = true} t) with cong {C[]} p≈ₒq .p-to-q t
... | q' , obs-t self tq s2 , p'≈q' = q' , obs-t self (indet tq) s2 , p'≈q'
... | q' , obs-t (cons ts s1) tq s2 , p'≈q' = q' , obs-t (cons (indet ts) s1) tq s2 , p'≈q'
p-to-q (cong {rename f C[]} p≈ₒq) (rename t) =
  let q' , obs-t sq1 tq sq2 , p'≈q' = cong {C[]} p≈ₒq .p-to-q t
  in rename f q' , obs-t (s-map rename sq1) (rename tq) (s-map rename sq2) , rename-respects-≈ p'≈q'
p-to-q (cong {hide f C[]} p≈ₒq) (hide {z = z} t) =
  let q' , obs-t s1 tq s2 , p'≈q' = cong {C[]} p≈ₒq .p-to-q t
  in hide f q' , obs-t (s-map hide s1) (hide {z = z} tq) (s-map hide s2) , hide-respects-≈ p'≈q'
p-to-q (cong {replace} p≈ₒq) = p≈ₒq .p-to-q
q-to-p (cong p≈ₒq) = cong (sym p≈ₒq) .p-to-q
