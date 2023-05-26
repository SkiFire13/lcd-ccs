open import Base

import ccs-vp.proc

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
-- X = Set of the variables
-- V = Set of the values
-- Args = Function that associated to every process name the type of its arguments
-- penv = Function from process names to the actual process,
--        given the values for the variables to be binded.
module ccs-vp.common (C N X V : Set) (Args : N → Set) (penv : ccs-vp.proc.PEnv C N X V Args) where

open import ccs-vp.proc C N X V Args public
open import ccs-vp.trans C N X V Args penv public
