{-# OPTIONS --safe #-}

open import Base

import ccs-vp.proc

module conv.trans (C N V : Set) (Args : N → Set) (penv : ccs-vp.proc.PEnv C N V Args) where

open import conv.proc C N V Args

open import ccs.common Conv-C Conv-N (conv-penv penv) as ccs
open import ccs-vp.common C N V Args penv as vp

-- Convert a transition from CCS VP to CCS.
-- Logically speaking this is proving that if there exist a transition
-- between two CCS VP processes then there exist also a corresponding
-- transition between the converted CCS processes.
conv-trans : ∀ {p₁ a p₂} → (p₁ -[ a ]→ᵥ p₂) → (conv-proc p₁ -[ conv-act a ]→ conv-proc p₂)
conv-trans send        = chan
conv-trans recv        = indet _ chan
conv-trans τ           = chan
conv-trans (par-L t)   = par-L (conv-trans t)
conv-trans (par-R t)   = par-R (conv-trans t)
conv-trans (par-B {a = a} tl tr) with a
... | send _ _         = par-B (conv-trans tl) (conv-trans tr)
... | recv _ _         = par-B (conv-trans tl) (conv-trans tr)
... | τ                = par-B (conv-trans tl) (conv-trans tr)
conv-trans (indet s t) = indet s (conv-trans t)
conv-trans (const t)   = const (conv-trans t)
conv-trans (rename {a = a} t) with a
... | send _ _         = rename (conv-trans t)
... | recv _ _         = rename (conv-trans t)
... | τ                = rename (conv-trans t)
conv-trans (hide {a = a} z t) with a
... | send _ _         = hide z (conv-trans t)
... | recv _ _         = hide z (conv-trans t)
... | τ                = hide z (conv-trans t)
conv-trans (if t)      = conv-trans t
