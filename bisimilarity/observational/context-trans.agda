{-# OPTIONS --safe --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.observational.context-trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv as ccs
open import bisimilarity.context C N penv
open import bisimilarity.observational.context C N penv renaming (sym to ̂≈-sym)
open import bisimilarity.observational.trans C N penv renaming (cong to ≈ₒ-cong)
open import bisimilarity.weak.base C N penv
open import bisimilarity.weak.properties C N penv renaming (reflexive to ≈-refl; sym to ≈-sym; trans to ≈-trans)
open import bisimilarity.weak.congruence C N penv

-- Prove that observational congruence defined by limiting self τ transitions
-- implies observational congruence defined as the contextual closure of weak bisimilarity.
≈ₒ→̂≈ : ∀ {p q} → p ≈ₒ q → p ̂≈ q
≈ₒ→̂≈ p≈ₒq = ≈+cong→̂≈ ≈ₒ→≈ ≈ₒ-cong p≈ₒq

NoUniversalProc : Set₁
NoUniversalProc = ∀ {p a} → ∃[ q ] ¬ (∃[ p' ] p =[ a ]⇒ p' × p' ≈ q)

-- (Try to) prove that observational congruence defined as the contextual closure of weak
-- bisimilarity implies observational congruence defined by limiting self τ transitions,
-- assuming C is inhabited.
̂≈→≈ₒ : C → NoUniversalProc → ∀ {p q} → p ̂≈ q → p ≈ₒ q
p⇒q (̂≈→≈ₒ _ _ C[p]≈C[q]) {a = send _} t with C[p]≈C[q] C[] .p⇒q (indet left t)
  where C[] = indet hole ccs.deadlock
... | q' , send self (indet left tq) s₂ , p'≈q' = q' , obs self tq s₂ , p'≈q'
... | _ , send self (indet right (indet () _)) _ , _
... | q' , send (cons (indet left tq) s₁) tq' s₂ , p'≈q' = q' , obs (cons tq s₁) tq' s₂ , p'≈q'
... | _ , send (cons (indet right (indet () _)) _) _ _ , _
p⇒q (̂≈→≈ₒ _ _ C[p]≈C[q]) {a = recv _} t with C[p]≈C[q] C[] .p⇒q (indet left t)
  where C[] = indet hole ccs.deadlock
... | q' , recv self (indet left tq) s₂ , p'≈q' = q' , obs self tq s₂ , p'≈q'
... | _ , recv self (indet right (indet () _)) _ , _
... | q' , recv (cons (indet left tq) s₁) tq' s₂ , p'≈q' = q' , obs (cons tq s₁) tq' s₂ , p'≈q'
... | _ , recv (cons (indet right (indet () _)) _) _ _ , _
p⇒q (̂≈→≈ₒ c ¬UProc C[p]≈C[q]) {a = τ} {p' = p'} t
  with r , ¬p'' ← ¬UProc {p'} {recv c}
  with C[p]≈C[q] (indet hole (act (recv c) r)) .p⇒q (indet left t)
... | q' , τ (cons (indet left tq) s) , p'≈q' = q' , obs self tq s , p'≈q'
... | q' , τ self , p'≈q' =
  let p'' , tp' , r≈p'' = p'≈q' .q⇒p (indet right act)
  in ⊥-elim (¬p'' (p'' , tp' , ≈-sym r≈p''))
q⇒p (̂≈→≈ₒ c ¬UProc C[p]≈C[q]) = ̂≈→≈ₒ c ¬UProc (̂≈-sym C[p]≈C[q]) .p⇒q

-- Prove that the assumption that C is inhabited is required for the previous theorem.
¬C→¬̂≈→≈ₒ : ¬ C → ¬ ∀ {p q} → p ̂≈ q → p ≈ₒ q
¬C→¬̂≈→≈ₒ ¬C ̂≈→≈ₒ with ̂≈→≈ₒ C[τd]≈C[d] .p⇒q act
  where
  C[τd]≈C[d] : act τ ccs.deadlock ̂≈ ccs.deadlock
  C[τd]≈C[d] = λ _ → ¬C→≈-always-true ¬C
... | _ , obs self (indet () _) _ , _
... | _ , obs (cons (indet () _) _) _ _ , _

-- Prove that NoUniversalProc is false when C is not inhabited
-- In particular when this happens every process is an universal process
-- because they can always do a self τ transition and remain bisimilar to q
¬C→¬NoUniversalProc : ¬ C → ¬ NoUniversalProc
¬C→¬NoUniversalProc ¬C ¬UProc =
  let q , ¬p' = ¬UProc {ccs.deadlock} {τ}
  in ¬p' (ccs.deadlock , τ self , ¬C→≈-always-true ¬C)

-- Prove that NoUniversalProc implies that C cannot possibly not be inhabited.
-- Constructively though this doesn't get us a value of C.
NoUniversalProc→¬¬C : NoUniversalProc → ¬ ¬ C
NoUniversalProc→¬¬C ¬UProc ¬C = ¬C→¬NoUniversalProc ¬C ¬UProc

-- It remains to be shown if C → NoUniversalProc or if ¬NoUniversalProc → ¬ ∀ {p q} → p ̂≈ q → p ≈ₒ q
