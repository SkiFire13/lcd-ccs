{-# OPTIONS --guardedness #-}

open import Base

import ccs.proc

module bisimilarity.strong.congruence (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.common C N penv
open import bisimilarity.context C N penv
open import bisimilarity.strong.base C N penv
open import bisimilarity.strong.properties C N penv

-- Lemma for helping proving cong
-- Prove that `Proc.par` respects strong bisimilarity
par-respects-~ : ∀ {pl pr ql qr} → pl ~ ql → pr ~ qr → par pl pr ~ par ql qr
q⇒p (par-respects-~ pl~ql pr~qr) = p⇒q (par-respects-~ (sym pl~ql) (sym pr~qr))
p⇒q (par-respects-~ {qr = qr} pl~ql pr~qr) (par-L {p' = p'} t) =
  let q' , t' , p'~q' = pl~ql .p⇒q t
  in  par q' qr , par-L t' , par-respects-~ p'~q' pr~qr
p⇒q (par-respects-~ {ql = ql} pl~ql pr~qr) (par-R {p' = p'} t) =
  let q' , t' , p'~q' = pr~qr .p⇒q t
  in  par ql q' , par-R t' , par-respects-~ pl~ql p'~q'
p⇒q (par-respects-~ pl~ql pr~qr) (par-B tl tr) =
  let ql' , tl' , pl'~ql' = pl~ql .p⇒q tl
      qr' , tr' , pr'~qr' = pr~qr .p⇒q tr
  in  par ql' qr' , par-B tl' tr' , par-respects-~ pl'~ql' pr'~qr'

-- Prove that ~ is a congruence
cong : Cong _~_
p⇒q (cong {chan a C} p~q) chan = subst C _ , chan , cong p~q
cong {par-L C r} p~q = par-respects-~ (cong p~q) reflexive
cong {par-R r C} p~q = par-respects-~ reflexive (cong p~q)
p⇒q (cong {indet C r} p~q) (indet right t) = _ , indet right t , reflexive
p⇒q (cong {indet C r} p~q) (indet left t) =
  let q' , t' , p'~q' = cong p~q .p⇒q t
  in  q' , indet left t' , p'~q'
p⇒q (cong {rename f C} p~q) (rename t) =
  let q' , t' , p'~q' = (cong {C} p~q) .p⇒q t
  in  rename f q' , rename t' , cong p'~q'
p⇒q (cong {hide f C} p~q) (hide z t) =
  let q' , t' , p'~q' = (cong {C} p~q) .p⇒q t
  in  hide f q' , hide z t' , cong p'~q'
p⇒q (cong {hole} p~q) = p~q .p⇒q
q⇒p (cong p~q) = p⇒q (cong (sym p~q))
