{-# OPTIONS --safe #-}

import ccs.proc

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
-- penv = "Process Environment" = Map from process names to the corresponding processes
module ccs.common (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.proc C N public
open import ccs.trans C N penv public
open import ccs.weak-trans C N penv public
