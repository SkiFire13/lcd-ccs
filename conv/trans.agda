open import Base

import ccs-vp.proc

module conv.trans (C N X V : Set) (Args : N → Set) (penv : ccs-vp.proc.PEnv C N X V Args) where

open import conv.proc C N X V Args

open import ccs.common Conv-C Conv-N (conv-penv penv) as ccs
open import ccs-vp.common C N X V Args penv as vp

-- Convert a transition from CCS VP to CCS, or in other words,
-- prove that if there's a transition between two CCS VP processes
-- then there's a corresponding transition between the converted processes too.
conv-trans : ∀ {p1 a p2} → (p1 -[ a ]→ᵥ p2) → (conv-proc p1 -[ conv-act a ]→ conv-proc p2)
conv-trans send        = chan
conv-trans recv        = indet _ chan
conv-trans tau         = chan
conv-trans (par-L t)   = par-L (conv-trans t)
conv-trans (par-R t)   = par-R (conv-trans t)
conv-trans (par-B {a = a} tl tr) with a
... | send _ _         = par-B (conv-trans tl) (conv-trans tr)
... | recv _ _         = par-B (conv-trans tl) (conv-trans tr)
... | tau              = par-B (conv-trans tl) (conv-trans tr)
conv-trans (indet s t) = indet s (conv-trans t)
conv-trans (const t)   = const (conv-trans t)
conv-trans (rename {a = a} t) with a
... | send _ _         = rename (conv-trans t)
... | recv _ _         = rename (conv-trans t)
... | tau              = rename (conv-trans t)
conv-trans (hide {a = a} z t) with a
... | send _ _         = hide z (conv-trans t)
... | recv _ _         = hide z (conv-trans t)
... | tau              = hide z (conv-trans t)
conv-trans (if t)      = conv-trans t
