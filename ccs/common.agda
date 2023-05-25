open import Data.Bool
open import Data.Empty

import ccs.proc

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
-- penv = Function from process names to the actual process
module ccs.common (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.proc C N public
open import ccs.trans C N penv public
open import ccs.weak-trans C N penv public
