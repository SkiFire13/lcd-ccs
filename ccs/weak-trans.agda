open import Data.Sum

import ccs.proc

module ccs.weak-trans {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.proc {C} {N}
open import ccs.trans {C} {N} {penv}

-- A (potentially empty) sequence of tau transitions
data TauSeq : Proc -> Proc -> Set₁ where
  self : forall {p} -> TauSeq p p
  cons : forall {p q r} -> Trans p tau q -> TauSeq q r -> TauSeq p r

-- Concatenate sequences of tau transitions
concat : forall {p q r} -> TauSeq p q -> TauSeq q r -> TauSeq p r
concat self t = t
concat (cons r t1) t2 = cons r (concat t1 t2)

-- A weak transition
data WeakTrans : Proc -> Act -> Proc -> Set₁ where
  send : forall {p q r s c} -> TauSeq p q -> Trans q (send c) r -> TauSeq r s -> WeakTrans p (send c) s
  recv : forall {p q r s c} -> TauSeq p q -> Trans q (recv c) r -> TauSeq r s -> WeakTrans p (recv c) s
  tau  : forall {p q} -> TauSeq p q -> WeakTrans p tau q

-- Convert a normal transition to a weak transition
trans-to-weak : forall {p a q} -> Trans p a q -> WeakTrans p a q
trans-to-weak {a = send c} r = send self r self
trans-to-weak {a = recv c} r = recv self r self
trans-to-weak {a = tau} r = tau (cons r self)

-- Joins a weak transitions with two tau weak transitions
join : forall {p q r s a} -> WeakTrans p tau q -> WeakTrans q a r -> WeakTrans r tau s -> WeakTrans p a s
join (tau s1) (send s2 r s3) (tau s4) = send (concat s1 s2) r (concat s3 s4)
join (tau s1) (recv s2 r s3) (tau s4) = recv (concat s1 s2) r (concat s3 s4)
join (tau s1) (tau s2) (tau s3) = tau (concat s1 (concat s2 s3))

-- Joins two weak tau transitions
join-tau : forall {p q r} -> WeakTrans p tau q -> WeakTrans q tau r -> WeakTrans p tau r
join-tau (tau s1) (tau s2) = tau (concat s1 s2)
