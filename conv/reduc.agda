open import Data.Bool

import ccs-vp.proc

module conv.reduc {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open import conv.proc {C} {N} {X} {V} {n-fv}

open import ccs {Conv-C} {Conv-N} {conv-penv penv} as ccs
open import ccs-vp {C} {N} {X} {V} {n-fv} {penv} as vp

-- Convert a reduction relation from CCS-VP to CCS, or in other words,
-- prove that if there's a reduction relation between two CCS-VP processes
-- then there's a corresponding relation between the converted processess too.
conv-reduc : forall {p1 c p2}
             -> vp.Reduc p1 c p2
             -> ccs.Reduc (conv-proc p1) (conv-act c) (conv-proc p2)
conv-reduc chan-send = chan
conv-reduc chan-recv = indet chan
conv-reduc chan-tau  = chan
conv-reduc (par-L r) = par-L (conv-reduc r)
conv-reduc (par-R r) = par-R (conv-reduc r)
conv-reduc (par-B {c} rl rr) with c
... | send _ _       = par-B (conv-reduc rl) (conv-reduc rr)
... | recv _ _       = par-B (conv-reduc rl) (conv-reduc rr)
... | tau            = par-B (conv-reduc rl) (conv-reduc rr)
conv-reduc (indet r) = indet (conv-reduc r)
conv-reduc (const r) = const (conv-reduc r)
conv-reduc (rename {c} r) with c
... | send _ _       = rename (conv-reduc r)
... | recv _ _       = rename (conv-reduc r)
... | tau            = rename (conv-reduc r)
conv-reduc (hide {c} {z = z} r) with c
... | send _ _       = hide {z = z} (conv-reduc r)
... | recv _ _       = hide {z = z} (conv-reduc r)
... | tau            = hide {z = z} (conv-reduc r)
conv-reduc (if r)    = conv-reduc r