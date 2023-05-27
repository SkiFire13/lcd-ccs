open import Base

import ccs-vp.proc

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
-- V = Set of the values
-- Args = Function that associated to every process name the type of its arguments
-- penv = "Process Environment" = Map from process names to the corresponding process functions
module ccs-vp.common (C N V : Set) (Args : N → Set) (penv : ccs-vp.proc.PEnv C N V Args) where

open import ccs-vp.proc C N V Args public
open import ccs-vp.trans C N V Args penv public
