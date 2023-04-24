open import Data.Sum

import ccs.proc
import ccs.reduc

module ccs.weak-reduc {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open ccs.proc {C} {N}
open ccs.reduc {C} {N} {penv}

data TauSeq : Proc -> Proc -> Set₁ where
  self : forall {p} -> TauSeq p p
  cons : forall {p q r} -> Reduc p tau q -> TauSeq q r -> TauSeq p r

data WeakReduc : Proc -> Act -> Proc -> Set₁ where
  send : forall {p q r s c} -> TauSeq p q -> Reduc q (send c) r -> TauSeq r s -> WeakReduc p (send c) s
  recv : forall {p q r s c} -> TauSeq p q -> Reduc q (recv c) r -> TauSeq r s -> WeakReduc p (recv c) s
  tau  : forall {p q} -> TauSeq p q -> WeakReduc p tau q

reduc-to-weak : forall {p a q} -> Reduc p a q -> WeakReduc p a q
reduc-to-weak {a = send c} r = send self r self
reduc-to-weak {a = recv c} r = recv self r self
reduc-to-weak {a = tau} r = tau (cons r self)
