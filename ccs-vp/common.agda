open import Data.Bool
open import Data.Empty

import ccs-vp.proc

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
-- X = Set of the variables
-- V = Set of the values
-- n-fv = Function that returns whether a constant will try to bind a given variable.
--        For example given the constant F(x) = a(x).0:
--        n-fv F x will return True because it will try to bind X
--        n-fv F y will return False because it will not try to bind y
--        Ideally we would track the binded/not binded variables with their values,
--        but that was somewhat problematic.
-- penv = Function from process names to the actual process,
--        given the values for the variables to be binded.
module ccs-vp.common {C N X V : Set} {n-fv : N -> X -> Bool} {penv : ccs-vp.proc.PEnv {C} {N} {X} {V} {n-fv}} where

open import ccs-vp.proc {C} {N} {X} {V} {n-fv} public
open import ccs-vp.trans {C} {N} {X} {V} {n-fv} {penv} public
