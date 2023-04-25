open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import ccs.proc

module bisimilarity.strong.congruence {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.common {C} {N} {penv}
open import bisimilarity.context {C} {N} {penv}
open import bisimilarity.strong.base {C} {N} {penv}
open import bisimilarity.strong.properties {C} {N} {penv}

-- Helper for cong
cong-par : forall {pl pr ql qr} -> pl ~ ql -> pr ~ qr -> par pl pr ~ par ql qr
q-to-p (cong-par pl~ql pr~qr) = p-to-q (cong-par (sym pl~ql) (sym pr~qr))
p-to-q (cong-par {qr = qr} pl~ql pr~qr) (par-L {p' = p'} t) =
  let q' , t' , p'~q' = pl~ql .p-to-q t
  in par q' qr , par-L t' , cong-par p'~q' pr~qr
p-to-q (cong-par {ql = ql} pl~ql pr~qr) (par-R {p' = p'} t) =
  let q' , t' , p'~q' = pr~qr .p-to-q t
  in par ql q' , par-R t' , cong-par pl~ql p'~q'
p-to-q (cong-par pl~ql pr~qr) (par-B {a} {pl' = pl'} {pr' = pr'} tl tr) =
  let ql' , tl' , pl'~ql' = pl~ql .p-to-q tl
      qr' , tr' , pr'~qr' = pr~qr .p-to-q tr
  in par ql' qr' , par-B tl' tr' , cong-par pl'~ql' pr'~qr'

-- Prove that ~ is a congruence
cong : forall {C[] p q} -> p ~ q -> subst C[] p ~ subst C[] q
cong p~q = helper refl refl p~q
  where
  helper : forall {C[] p q ps qs} -> ps ≡ subst C[] p -> qs ≡ subst C[] q -> p ~ q -> ps ~ qs

  p-to-q (helper {chan a C[]} {q = q} refl refl p~q) chan = subst C[] q , chan , cong p~q

  helper {par c1 c2} refl refl p~q = cong-par (cong {c1} p~q) (cong {c2} p~q)

  p-to-q (helper {indet f} refl refl p~q) (indet {s = s} t) =
    let q' , t' , p'~q' = (cong {f s} p~q) .p-to-q t
    in q' , indet {s = s} t' , p'~q'

  helper {const _} refl refl _ = reflexive

  p-to-q (helper {rename f C[]} refl refl p~q) (rename {a = a} t) =
    let q' , t' , p'~q' = (cong {C[]} p~q) .p-to-q t
    in rename f q' , rename {a = a} t' , cong p'~q'

  p-to-q (helper {hide f C[]} refl refl p~q) (hide {z = z} t) =
    let q' , t' , p'~q' = (cong {C[]} p~q) .p-to-q t
    in hide f q' , hide {z = z} t' , cong p'~q'

  helper {replace} refl refl p~q = p~q

  -- The other half be proved through symmetry
  q-to-p (helper refl refl p~q) = p-to-q (helper refl refl (sym p~q))
