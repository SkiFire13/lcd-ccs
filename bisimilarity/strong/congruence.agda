{-# OPTIONS --guardedness #-}

open import Data.Bool
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl; inspect; [_])

import ccs.proc

module bisimilarity.strong.congruence {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.cong {C} {N} {penv}
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.strong.base {C} {N} {penv}
open import bisimilarity.strong.properties {C} {N} {penv}

-- Helper for cong
par-respects-~ : forall {pl pr ql qr} -> pl ~ ql -> pr ~ qr -> par pl pr ~ par ql qr
q-to-p (par-respects-~ pl~ql pr~qr) = p-to-q (par-respects-~ (sym pl~ql) (sym pr~qr))
p-to-q (par-respects-~ {qr = qr} pl~ql pr~qr) (par-L {p' = p'} t) =
  let q' , t' , p'~q' = pl~ql .p-to-q t
  in par q' qr , par-L t' , par-respects-~ p'~q' pr~qr
p-to-q (par-respects-~ {ql = ql} pl~ql pr~qr) (par-R {p' = p'} t) =
  let q' , t' , p'~q' = pr~qr .p-to-q t
  in par ql q' , par-R t' , par-respects-~ pl~ql p'~q'
p-to-q (par-respects-~ pl~ql pr~qr) (par-B {a} {pl' = pl'} {pr' = pr'} tl tr) =
  let ql' , tl' , pl'~ql' = pl~ql .p-to-q tl
      qr' , tr' , pr'~qr' = pr~qr .p-to-q tr
  in par ql' qr' , par-B tl' tr' , par-respects-~ pl'~ql' pr'~qr'

-- Prove that ~ is a congruence
cong : Cong _~_
p-to-q (cong {chan a C[]} p~q) chan = subst C[] _ , chan , cong p~q
cong {par-L C[] r} p~q = par-respects-~ (cong p~q) reflexive
cong {par-R r C[]} p~q = par-respects-~ reflexive (cong p~q)
p-to-q (cong {indet C[] r} p~q) (indet {s = false} t) = -, indet {s = false} t , reflexive
p-to-q (cong {indet C[] r} p~q) (indet {s = true} t) =
  let q' , t' , p'~q' = cong p~q .p-to-q t
  in q' , indet t' , p'~q'
p-to-q (cong {rename f C[]} p~q) (rename {a = a} t) =
  let q' , t' , p'~q' = (cong {C[]} p~q) .p-to-q t
  in rename f q' , rename {a = a} t' , cong p'~q'
p-to-q (cong {hide f C[]} p~q) (hide {z = z} t) =
  let q' , t' , p'~q' = (cong {C[]} p~q) .p-to-q t
  in hide f q' , hide {z = z} t' , cong p'~q'
p-to-q (cong {replace} p~q) = p~q .p-to-q
q-to-p (cong p~q) = p-to-q (cong (sym p~q))

-- Helper to prove that compose is the same as composing subst under strong bisimilarity
ss~sc : forall {C1[] C2[] p} -> subst C1[] (subst C2[] p) ~ subst (compose C1[] C2[]) p
ss~sc {chan a C[]} = cong {chan a replace} (ss~sc {C[]})
ss~sc {par-L C[] p} = cong {par-L replace p} (ss~sc {C[]})
ss~sc {par-R p C[]} = cong {par-R p replace} (ss~sc {C[]})
p-to-q (ss~sc {indet C[] _}) (indet {s = s} t) with s
... | true = let q' , t' , p'~q' = ss~sc {C[]} .p-to-q t in q' , indet {s = true} t' , p'~q'
... | false = _ , indet {s = false} t , reflexive
q-to-p (ss~sc {indet C[] _}) (indet {s = s} t) with s
... | true = let q' , t' , p'~q' = ss~sc {C[]} .q-to-p t in q' , indet {s = true} t' , p'~q'
... | false = _ , indet {s = false} t , reflexive
ss~sc {rename f C[]} = cong {rename f replace} (ss~sc {C[]})
ss~sc {hide f C[]} = cong {hide f replace} (ss~sc {C[]})
ss~sc {replace} = reflexive
