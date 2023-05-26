open import Base

import ccs.proc

module ccs.weak-trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.proc C N
open import ccs.trans C N penv

private
  variable
    {p q r} : Proc
    {p1 p2 p3 p4} : Proc
    {pl pr ql qr} : Proc
    {a} : Act
    {c} : C

-- A (potentially empty) sequence of tau transitions
data _-[tau]→*_ : Proc → Proc → Set₁ where
  self : p -[tau]→* p
  cons : (p1 -[ tau ]→ p2) → (p2 -[tau]→* p3) → (p1 -[tau]→* p3)

-- Concatenate sequences of tau transitions
concat : (p1 -[tau]→* p2) → (p2 -[tau]→* p3) → (p1 -[tau]→* p3)
concat self        t  = t
concat (cons t t1) t2 = cons t (concat t1 t2)

-- A weak transition
data _=[_]⇒_ : Proc → Act → Proc → Set₁ where
  send : (p1 -[tau]→* p2) → (p2 -[ send c ]→ p3) → (p3 -[tau]→* p4) → (p1 =[ send c ]⇒ p4)
  recv : (p1 -[tau]→* p2) → (p2 -[ recv c ]→ p3) → (p3 -[tau]→* p4) → (p1 =[ recv c ]⇒ p4)
  tau  : (p1 -[tau]→* p2) → (p1 =[ tau ]⇒ p2)

-- Convert a normal transition to a weak transition
trans→weak : (p -[ a ]→ q) → (p =[ a ]⇒ q)
trans→weak {a = send c} t = send self t self
trans→weak {a = recv c} t = recv self t self
trans→weak {a = tau}    t = tau (cons t self)

-- Joins a weak transitions with two tau weak transitions
join : (p1 =[ tau ]⇒ p2) → (p2 =[ a ]⇒ p3) → (p3 =[ tau ]⇒ p4) → (p1 =[ a ]⇒ p4)
join (tau s1) (send s2 t s3) (tau s4) = send (concat s1 s2) t (concat s3 s4)
join (tau s1) (recv s2 t s3) (tau s4) = recv (concat s1 s2) t (concat s3 s4)
join (tau s1) (tau s2)       (tau s3) = tau (concat s1 (concat s2 s3))

-- Joins two weak tau transitions
join-tau : (p1 =[ tau ]⇒ p2) → (p2 =[ tau ]⇒ p3) → (p1 =[ tau ]⇒ p3)
join-tau (tau s1) (tau s2) = tau (concat s1 s2)

-- Maps each transition in a TauSeq
s-map : {f : Proc → Proc} → (g : ∀ {p q} → (p -[ tau ]→ q) → (f p -[ tau ]→ f q))
        → (p -[tau]→* q) → (f p -[tau]→* f q)
s-map {f = f} g self       = self
s-map {f = f} g (cons t s) = cons (g t) (s-map g s)

-- Maps each transition in a WeakTrans
w-map : {f : Proc → Proc} → (g : ∀ {p q a} → (p -[ a ]→ q) → (f p -[ a ]→ f q))
        → (p =[ a ]⇒ q) → (f p =[ a ]⇒ f q)
w-map {f = f} g (send s1 t s2) = send (s-map g s1) (g t) (s-map g s2)
w-map {f = f} g (recv s1 t s2) = recv (s-map g s1) (g t) (s-map g s2)
w-map {f = f} g (tau s)        = tau (s-map g s)

-- Like Trans.par-B but for weak transitions
w-par-B : (pl =[ a ]⇒ ql) → (pr =[ flip-act a ]⇒ qr) → (par pl pr =[ tau ]⇒ par ql qr)
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
w-hide : ∀ {f} → filter-act f a → (p =[ a ]⇒ q) → (hide f p =[ a ]⇒ hide f q)
w-hide z (send s1 t s2) = send (s-map (hide tt) s1) (hide z t) (s-map (hide tt) s2)
w-hide z (recv s1 t s2) = recv (s-map (hide tt) s1) (hide z t) (s-map (hide tt) s2)
w-hide z (tau s)        = tau (s-map (hide tt) s)

-- Like Trans.rename but for weak transitions
w-rename : ∀ {f} → (p =[ a ]⇒ q) → (rename f p =[ map-act f a ]⇒ rename f q)
w-rename (send s1 t s2) = send (s-map rename s1) (rename t) (s-map rename s2)
w-rename (recv s1 t s2) = recv (s-map rename s1) (rename t) (s-map rename s2)
w-rename (tau s)        = tau (s-map rename s)
