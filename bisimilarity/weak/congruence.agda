{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Empty
open import Data.Product
open import Relation.Nullary

import ccs.proc

module bisimilarity.weak.congruence {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv} as ccs
open import bisimilarity.context {C} {N} {penv} as ctx
open import bisimilarity.weak.base {C} {N} {penv}
open import bisimilarity.weak.properties {C} {N} {penv}

-- Prove that ≈ is not a congruence
≈-not-cong : {c : C} -> ¬ forall {C[] p q} -> p ≈ q -> subst C[] p ≈ subst C[] q
≈-not-cong {c} cong with cong {C[]} τd≈d .p-to-q (indet {s = true} chan)
  where
  τd≈d : chan tau ccs.deadlock ≈ ccs.deadlock
  p-to-q τd≈d chan = ccs.deadlock , tau self , reflexive
  q-to-p τd≈d (indet {s = ()} _)
  C[] = indet replace (chan (send c) ccs.deadlock)
... | _ , tau (cons (indet {s = true} (indet {s = ()} _)) _) , _
... | _ , tau self , d≈c[d] with d≈c[d] .q-to-p (indet {s = false} chan)
...   | _ , send self (indet {s = ()} _) _ , _
...   | _ , send (cons (indet {s = ()} _) _) _ _ , _

≈-trivial-if-not-c : ¬ C -> forall {p q} -> p ≈ q
p-to-q (≈-trivial-if-not-c ¬c) {send c} _ = ⊥-elim (¬c c)
p-to-q (≈-trivial-if-not-c ¬c) {recv c} _ = ⊥-elim (¬c c)
p-to-q (≈-trivial-if-not-c ¬c {q = q}) {tau} t = q , tau self , ≈-trivial-if-not-c ¬c
q-to-p (≈-trivial-if-not-c ¬c) {send c} _ = ⊥-elim (¬c c)
q-to-p (≈-trivial-if-not-c ¬c) {recv c} _ = ⊥-elim (¬c c)
q-to-p (≈-trivial-if-not-c ¬c {p = p}) {tau} t = p , tau self , ≈-trivial-if-not-c ¬c

-- Prove that ≈ respects all the other kind of contexts

chan-respects-≈ : forall {a p q} -> p ≈ q -> chan a p ≈ chan a q
p-to-q (chan-respects-≈ {q = q} p≈q) chan = q , trans-to-weak chan , p≈q
q-to-p (chan-respects-≈ {p = p} p≈q) chan = p , trans-to-weak chan , sym p≈q

par-respects-≈ : forall {pl ql pr qr} -> pl ≈ ql -> pr ≈ qr -> par pl pr ≈ par ql qr
q-to-p (par-respects-≈ pl~ql pr~qr) = p-to-q (par-respects-≈ (sym pl~ql) (sym pr~qr))
p-to-q (par-respects-≈ {qr = qr} pl~ql pr~qr) (par-L {p' = p'} t) =
  let q' , t' , p'~q' = pl~ql .p-to-q t
  in par q' qr , w-map par-L t' , par-respects-≈ p'~q' pr~qr
p-to-q (par-respects-≈ {ql = ql} pl~ql pr~qr) (par-R {p' = p'} t) =
  let q' , t' , p'~q' = pr~qr .p-to-q t
  in par ql q' , w-map par-R t' , par-respects-≈ pl~ql p'~q'
p-to-q (par-respects-≈ pl~ql pr~qr) (par-B {a} {pl' = pl'} {pr' = pr'} tl tr) =
  let ql' , tl' , pl'~ql' = pl~ql .p-to-q tl
      qr' , tr' , pr'~qr' = pr~qr .p-to-q tr
  in par ql' qr' , w-par-B tl' tr' , par-respects-≈ pl'~ql' pr'~qr'

hide-respects-≈ : forall {f p q} -> p ≈ q -> hide f p ≈ hide f q
p-to-q (hide-respects-≈ {f} p≈q) (hide {z = z} t) =
  let q' , t' , p'≈q' = p≈q .p-to-q t
  in hide f q' , w-hide {z = z} t' , hide-respects-≈ p'≈q'
q-to-p (hide-respects-≈ p≈q) = p-to-q (hide-respects-≈ (sym p≈q))

rename-respects-≈ : forall {f p q} -> p ≈ q -> rename f p ≈ rename f q
p-to-q (rename-respects-≈ {f} p≈q) (rename t) =
  let q' , t' , p'≈q' = p≈q .p-to-q t
  in rename f q' , w-rename t' , rename-respects-≈ p'≈q'
q-to-p (rename-respects-≈ p≈q) = p-to-q (rename-respects-≈ (sym p≈q))
