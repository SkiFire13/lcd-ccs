open import Data.Sum

import ccs.proc

module ccs.weak-trans {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.proc {C} {N}
open import ccs.trans {C} {N} {penv}

private
  variable
    {p q} : Proc
    {p1 p2 p3 p4} : Proc
    {a} : Act
    {c} : C

-- A (potentially empty) sequence of tau transitions
data TauSeq : Proc -> Proc -> Set₁ where
  self : TauSeq p p
  cons : Trans p1 tau p2 -> TauSeq p2 p3 -> TauSeq p1 p3

-- Concatenate sequences of tau transitions
concat : TauSeq p1 p2 -> TauSeq p2 p3 -> TauSeq p1 p3
concat self t = t
concat (cons t t1) t2 = cons t (concat t1 t2)

-- A weak transition
data WeakTrans : Proc -> Act -> Proc -> Set₁ where
  send : TauSeq p1 p2 -> Trans p2 (send c) p3 -> TauSeq p3 p4 -> WeakTrans p1 (send c) p4
  recv : TauSeq p1 p2 -> Trans p2 (recv c) p3 -> TauSeq p3 p4 -> WeakTrans p1 (recv c) p4
  tau  : TauSeq p1 p2 -> WeakTrans p1 tau p2

-- Convert a normal transition to a weak transition
trans-to-weak : Trans p a q -> WeakTrans p a q
trans-to-weak {a = send c} t = send self t self
trans-to-weak {a = recv c} t = recv self t self
trans-to-weak {a = tau} t = tau (cons t self)

-- Joins a weak transitions with two tau weak transitions
join : WeakTrans p1 tau p2 -> WeakTrans p2 a p3 -> WeakTrans p3 tau p4 -> WeakTrans p1 a p4
join (tau s1) (send s2 t s3) (tau s4) = send (concat s1 s2) t (concat s3 s4)
join (tau s1) (recv s2 t s3) (tau s4) = recv (concat s1 s2) t (concat s3 s4)
join (tau s1) (tau s2) (tau s3) = tau (concat s1 (concat s2 s3))

-- Joins two weak tau transitions
join-tau : WeakTrans p1 tau p2 -> WeakTrans p2 tau p3 -> WeakTrans p1 tau p3
join-tau (tau s1) (tau s2) = tau (concat s1 s2)
