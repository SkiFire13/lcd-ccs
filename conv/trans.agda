open import Data.Bool

import ccs-vp.proc

module conv.trans {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open import conv.proc {C} {N} {X} {V} {n-fv}

open import ccs.common {Conv-C} {Conv-N} {conv-penv penv} as ccs
open import ccs-vp.common {C} {N} {X} {V} {n-fv} {penv} as vp

-- Convert a transition from CCS VP to CCS, or in other words,
-- prove that if there's a transition between two CCS VP processes
-- then there's a corresponding transition between the converted processes too.
conv-trans : forall {p1 a p2}
             -> vp.Trans p1 a p2
             -> ccs.Trans (conv-proc p1) (conv-act a) (conv-proc p2)
conv-trans send      = chan
conv-trans recv      = indet chan
conv-trans tau       = chan
conv-trans (par-L r) = par-L (conv-trans r)
conv-trans (par-R r) = par-R (conv-trans r)
conv-trans (par-B {a} rl rr) with a
... | send _ _       = par-B (conv-trans rl) (conv-trans rr)
... | recv _ _       = par-B (conv-trans rl) (conv-trans rr)
... | tau            = par-B (conv-trans rl) (conv-trans rr)
conv-trans (indet r) = indet (conv-trans r)
conv-trans (const r) = const (conv-trans r)
conv-trans (rename {a} r) with a
... | send _ _       = rename (conv-trans r)
... | recv _ _       = rename (conv-trans r)
... | tau            = rename (conv-trans r)
conv-trans (hide {a} {z = z} r) with a
... | send _ _       = hide {z = z} (conv-trans r)
... | recv _ _       = hide {z = z} (conv-trans r)
... | tau            = hide {z = z} (conv-trans r)
conv-trans (if r)    = conv-trans r
