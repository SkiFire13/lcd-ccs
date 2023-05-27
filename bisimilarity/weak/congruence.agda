{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.weak.congruence (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.context C N penv as ctx
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv

-- Prove that ≈ is not a congruence, assuming that C is inhabited
¬≈-cong : C → ¬ ∀ {C p q} → p ≈ q → subst C p ≈ subst C q
¬≈-cong c cong with cong {h+cd} τd≈d .p⇒q (indet left chan)
  where
  h+cd = indet hole (chan (send c) ccs.deadlock)
  τd≈d : chan τ ccs.deadlock ≈ ccs.deadlock
  p⇒q τd≈d chan = ccs.deadlock , τ self , reflexive
  q⇒p τd≈d (indet () _)
... | _ , τ (cons (indet left (indet () _)) _) , _
... | _ , τ self , d≈C[d] with d≈C[d] .q⇒p (indet right chan)
...   | _ , send self (indet () _) _ , _
...   | _ , send (cons (indet () _) _) _ _ , _

-- Prove that an instance of C is not actually needed, just a proof that
-- C cannot be empty
¬≈-cong' : ¬ ¬ C → ¬ ∀ {C p q} → p ≈ q → subst C p ≈ subst C q
¬≈-cong' ¬¬C cong = ¬¬C (λ c → ¬≈-cong c cong)

-- Proof that if C is not inhabited then ≈ is always inhabited
¬c→≈-always-true : ¬ C → ∀ {p q} → p ≈ q
p⇒q (¬c→≈-always-true ¬c) {send c} _ = ⊥-elim (¬c c)
p⇒q (¬c→≈-always-true ¬c) {recv c} _ = ⊥-elim (¬c c)
p⇒q (¬c→≈-always-true ¬c) {τ}      t = _ , τ self , ¬c→≈-always-true ¬c
q⇒p (¬c→≈-always-true ¬c) {send c} _ = ⊥-elim (¬c c)
q⇒p (¬c→≈-always-true ¬c) {recv c} _ = ⊥-elim (¬c c)
q⇒p (¬c→≈-always-true ¬c) {τ}      t = _ , τ self , ¬c→≈-always-true ¬c
-- And thus ≈ is trivially a congruence
¬c→≈-cong : ¬ C → Cong _≈_
¬c→≈-cong ¬c _ = ¬c→≈-always-true ¬c

-- Prove that all the contexts except indet respects ≈

chan-respects-≈ : ∀ {a p q} → p ≈ q → chan a p ≈ chan a q
p⇒q (chan-respects-≈ {q = q} p≈q) chan = q , trans→weak chan , p≈q
q⇒p (chan-respects-≈ {p = p} p≈q) chan = p , trans→weak chan , sym p≈q

par-respects-≈ : ∀ {pl ql pr qr} → pl ≈ ql → pr ≈ qr → par pl pr ≈ par ql qr
p⇒q (par-respects-≈ {qr = qr} pl~ql pr~qr) (par-L t) =
  let q' , t' , p'~q' = pl~ql .p⇒q t
  in  par q' qr , map-w par-L t' , par-respects-≈ p'~q' pr~qr
p⇒q (par-respects-≈ {ql = ql} pl~ql pr~qr) (par-R t) =
  let q' , t' , p'~q' = pr~qr .p⇒q t
  in  par ql q' , map-w par-R t' , par-respects-≈ pl~ql p'~q'
p⇒q (par-respects-≈ pl~ql pr~qr) (par-B tl tr) =
  let ql' , tl' , pl'~ql' = pl~ql .p⇒q tl
      qr' , tr' , pr'~qr' = pr~qr .p⇒q tr
  in  par ql' qr' , par-B-w tl' tr' , par-respects-≈ pl'~ql' pr'~qr'
q⇒p (par-respects-≈ pl~ql pr~qr) = p⇒q (par-respects-≈ (sym pl~ql) (sym pr~qr))

hide-respects-≈ : ∀ {f p q} → p ≈ q → hide f p ≈ hide f q
p⇒q (hide-respects-≈ {f} p≈q) (hide z t) =
  let q' , t' , p'≈q' = p≈q .p⇒q t
  in  hide f q' , hide-w z t' , hide-respects-≈ p'≈q'
q⇒p (hide-respects-≈ p≈q) = p⇒q (hide-respects-≈ (sym p≈q))

rename-respects-≈ : ∀ {f p q} → p ≈ q → rename f p ≈ rename f q
p⇒q (rename-respects-≈ {f} p≈q) (rename t) =
  let q' , t' , p'≈q' = p≈q .p⇒q t
  in  rename f q' , rename-w t' , rename-respects-≈ p'≈q'
q⇒p (rename-respects-≈ p≈q) = p⇒q (rename-respects-≈ (sym p≈q))
