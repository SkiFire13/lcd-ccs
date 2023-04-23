open import Data.Bool
open import Data.Empty

import ccs.proc
import ccs.reduc

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
-- penv = Function from process names to the actual process
module ccs {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open ccs.proc {C} {N} public
open ccs.reduc {C} {N} {penv} public
