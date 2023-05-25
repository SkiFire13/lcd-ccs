{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Relation.Nullary

import ccs.proc

module bisimilarity.weak.congruence (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.cong C N penv
open import bisimilarity.context C N penv as ctx
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv

-- Prove that ≈ is not a congruence
≈-not-cong : {c : C} → ¬ ∀ {C[] p q} → p ≈ q → subst C[] p ≈ subst C[] q
≈-not-cong {c} cong with cong {C[]} τd≈d .p⇒q (indet {s = true} chan)
  where
  τd≈d : chan tau ccs.deadlock ≈ ccs.deadlock
  p⇒q τd≈d chan = ccs.deadlock , tau self , reflexive
  q⇒p τd≈d (indet {s = ()} _)
  C[] = indet replace (chan (send c) ccs.deadlock)
... | _ , tau (cons (indet {s = true} (indet {s = ()} _)) _) , _
... | _ , tau self , d≈C[d] with d≈C[d] .q⇒p (indet {s = false} chan)
...   | _ , send self (indet {s = ()} _) _ , _
...   | _ , send (cons (indet {s = ()} _) _) _ _ , _

-- Prove that the c requisite above is required, otherwise ≈ becomes always true
¬c→≈-always-true : ¬ C → ∀ {p q} → p ≈ q
p⇒q (¬c→≈-always-true ¬c) {send c} _ = ⊥-elim (¬c c)
p⇒q (¬c→≈-always-true ¬c) {recv c} _ = ⊥-elim (¬c c)
p⇒q (¬c→≈-always-true ¬c) {tau} t = -, tau self , ¬c→≈-always-true ¬c
q⇒p (¬c→≈-always-true ¬c) {send c} _ = ⊥-elim (¬c c)
q⇒p (¬c→≈-always-true ¬c) {recv c} _ = ⊥-elim (¬c c)
q⇒p (¬c→≈-always-true ¬c) {tau} t = -, tau self , ¬c→≈-always-true ¬c
-- And thus ≈ is trivially a congruence
¬c→≈-cong : ¬ C → Cong _≈_
¬c→≈-cong ¬c _ = ¬c→≈-always-true ¬c

-- Prove that ≈ respects all the other kind of contexts

chan-respects-≈ : ∀ {a p q} → p ≈ q → chan a p ≈ chan a q
p⇒q (chan-respects-≈ {q = q} p≈q) chan = q , trans→weak chan , p≈q
q⇒p (chan-respects-≈ {p = p} p≈q) chan = p , trans→weak chan , sym p≈q

par-respects-≈ : ∀ {pl ql pr qr} → pl ≈ ql → pr ≈ qr → par pl pr ≈ par ql qr
p⇒q (par-respects-≈ {qr = qr} pl~ql pr~qr) (par-L {p' = p'} t) =
  let q' , t' , p'~q' = pl~ql .p⇒q t
  in par q' qr , w-map par-L t' , par-respects-≈ p'~q' pr~qr
p⇒q (par-respects-≈ {ql = ql} pl~ql pr~qr) (par-R {p' = p'} t) =
  let q' , t' , p'~q' = pr~qr .p⇒q t
  in par ql q' , w-map par-R t' , par-respects-≈ pl~ql p'~q'
p⇒q (par-respects-≈ pl~ql pr~qr) (par-B {a} {pl' = pl'} {pr' = pr'} tl tr) =
  let ql' , tl' , pl'~ql' = pl~ql .p⇒q tl
      qr' , tr' , pr'~qr' = pr~qr .p⇒q tr
  in par ql' qr' , w-par-B tl' tr' , par-respects-≈ pl'~ql' pr'~qr'
q⇒p (par-respects-≈ pl~ql pr~qr) = p⇒q (par-respects-≈ (sym pl~ql) (sym pr~qr))

hide-respects-≈ : ∀ {f p q} → p ≈ q → hide f p ≈ hide f q
p⇒q (hide-respects-≈ {f} p≈q) (hide {z = z} t) =
  let q' , t' , p'≈q' = p≈q .p⇒q t
  in hide f q' , w-hide {z = z} t' , hide-respects-≈ p'≈q'
q⇒p (hide-respects-≈ p≈q) = p⇒q (hide-respects-≈ (sym p≈q))

rename-respects-≈ : ∀ {f p q} → p ≈ q → rename f p ≈ rename f q
p⇒q (rename-respects-≈ {f} p≈q) (rename t) =
  let q' , t' , p'≈q' = p≈q .p⇒q t
  in rename f q' , w-rename t' , rename-respects-≈ p'≈q'
q⇒p (rename-respects-≈ p≈q) = p⇒q (rename-respects-≈ (sym p≈q))
