open import Data.Sum

import ccs.proc

module ccs.weak-reduc {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.proc {C} {N}
open import ccs.reduc {C} {N} {penv}

-- A (potentially empty) sequence of tau reductions
data TauSeq : Proc -> Proc -> Set₁ where
  self : forall {p} -> TauSeq p p
  cons : forall {p q r} -> Reduc p tau q -> TauSeq q r -> TauSeq p r

-- Concatenate sequences of tau reductions
concat : forall {p q r} -> TauSeq p q -> TauSeq q r -> TauSeq p r
concat self t = t
concat (cons r t1) t2 = cons r (concat t1 t2)

-- A weak reduction
data WeakReduc : Proc -> Act -> Proc -> Set₁ where
  send : forall {p q r s c} -> TauSeq p q -> Reduc q (send c) r -> TauSeq r s -> WeakReduc p (send c) s
  recv : forall {p q r s c} -> TauSeq p q -> Reduc q (recv c) r -> TauSeq r s -> WeakReduc p (recv c) s
  tau  : forall {p q} -> TauSeq p q -> WeakReduc p tau q

-- Convert a normal reduction to a weak reduction
reduc-to-weak : forall {p a q} -> Reduc p a q -> WeakReduc p a q
reduc-to-weak {a = send c} r = send self r self
reduc-to-weak {a = recv c} r = recv self r self
reduc-to-weak {a = tau} r = tau (cons r self)

-- Joins a weak reductions with two tau weak reductions
join : forall {p q r s a} -> WeakReduc p tau q -> WeakReduc q a r -> WeakReduc r tau s -> WeakReduc p a s
join (tau s1) (send s2 r s3) (tau s4) = send (concat s1 s2) r (concat s3 s4)
join (tau s1) (recv s2 r s3) (tau s4) = recv (concat s1 s2) r (concat s3 s4)
join (tau s1) (tau s2) (tau s3) = tau (concat s1 (concat s2 s3))

-- Joins two weak tau reductions
join-tau : forall {p q r} -> WeakReduc p tau q -> WeakReduc q tau r -> WeakReduc p tau r
join-tau (tau s1) (tau s2) = tau (concat s1 s2)
