open import Data.Bool
open import Data.Sum
open import Data.Unit

import ccs.proc

module ccs.weak-trans {C N : Set} {penv : ccs.proc.PEnv {C} {N}} where

open import ccs.proc {C} {N}
open import ccs.trans {C} {N} {penv}

private
  variable
    {p q r} : Proc
    {p1 p2 p3 p4} : Proc
    {pl pr ql qr} : Proc
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

-- Maps each transition in a TauSeq
s-map : {f : Proc -> Proc} -> (g : forall {p q} -> Trans p tau q -> Trans (f p) tau (f q))
        -> TauSeq p q -> TauSeq (f p) (f q)
s-map {f = f} g self = self
s-map {f = f} g (cons t s) = cons (g t) (s-map g s)

-- Maps each transition in a WeakTrans
w-map : {f : Proc -> Proc} -> (g : forall {p q a} -> Trans p a q -> Trans (f p) a (f q))
        -> WeakTrans p a q -> WeakTrans (f p) a (f q)
w-map {f = f} g (send s1 t s2) = send (s-map g s1) (g t) (s-map g s2)
w-map {f = f} g (recv s1 t s2) = recv (s-map g s1) (g t) (s-map g s2)
w-map {f = f} g (tau s) = tau (s-map g s)

-- Like Trans.par-B but for weak transitions
w-par-B : WeakTrans pl a ql -> WeakTrans pr (flip-act a) qr -> WeakTrans (par pl pr) tau (par ql qr)
w-par-B (send sl1 tl sl2) (recv sr1 tr sr2) =
  let s1 = concat (s-map par-L sl1) (s-map par-R sr1)
      s2 = concat (s-map par-L sl2) (s-map par-R sr2)
  in tau (concat s1 (cons (par-B tl tr) s2))
w-par-B (recv sl1 tl sl2) (send sr1 tr sr2) =
  let s1 = concat (s-map par-L sl1) (s-map par-R sr1)
      s2 = concat (s-map par-L sl2) (s-map par-R sr2)
  in tau (concat s1 (cons (par-B tl tr) s2))
w-par-B (tau sl) (tau sr) = tau (concat (s-map par-L sl) (s-map par-R sr))

-- Like Trans.hide but for weak transitions
w-hide : forall {f} -> {z : T (filter-act f a)} -> WeakTrans p a q -> WeakTrans (hide f p) a (hide f q)
w-hide {z = z} (send s1 t s2) = send (s-map hide s1) (hide {z = z} t) (s-map hide s2)
w-hide {z = z} (recv s1 t s2) = recv (s-map hide s1) (hide {z = z} t) (s-map hide s2)
w-hide (tau s) = tau (s-map hide s)

-- Like Trans.rename but for weak transitions
w-rename : forall {f} -> WeakTrans p a q -> WeakTrans (rename f p) (map-action f a) (rename f q)
w-rename (send s1 t s2) = send (s-map rename s1) (rename t) (s-map rename s2)
w-rename (recv s1 t s2) = recv (s-map rename s1) (rename t) (s-map rename s2)
w-rename (tau s) = tau (s-map rename s)
