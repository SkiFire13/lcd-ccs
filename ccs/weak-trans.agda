open import Base

import ccs.proc

module ccs.weak-trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.proc C N
open import ccs.trans C N penv

private
  variable
    {p q r} : Proc
    {p₁ p₂ p₃ p₄} : Proc
    {pl pr ql qr} : Proc
    {a} : Act
    {c} : C

-- A (potentially empty) sequence of tau transitions
data _-[tau]→*_ : Proc → Proc → Set₁ where
  self : p -[tau]→* p
  cons : (p₁ -[ tau ]→ p₂) → (p₂ -[tau]→* p₃) → (p₁ -[tau]→* p₃)

-- Concatenate sequences of tau transitions
concat : (p₁ -[tau]→* p₂) → (p₂ -[tau]→* p₃) → (p₁ -[tau]→* p₃)
concat self        t  = t
concat (cons t t₁) t₂ = cons t (concat t₁ t₂)

-- A weak transition
data _=[_]⇒_ : Proc → Act → Proc → Set₁ where
  send : (p₁ -[tau]→* p₂) → (p₂ -[ send c ]→ p₃) → (p₃ -[tau]→* p₄) → (p₁ =[ send c ]⇒ p₄)
  recv : (p₁ -[tau]→* p₂) → (p₂ -[ recv c ]→ p₃) → (p₃ -[tau]→* p₄) → (p₁ =[ recv c ]⇒ p₄)
  tau  : (p₁ -[tau]→* p₂) → (p₁ =[ tau ]⇒ p₂)

-- Convert a normal transition to a weak transition
trans→weak : (p -[ a ]→ q) → (p =[ a ]⇒ q)
trans→weak {a = send c} t = send self t self
trans→weak {a = recv c} t = recv self t self
trans→weak {a = tau}    t = tau (cons t self)

-- Joins a weak transitions with two tau weak transitions
join : (p₁ =[ tau ]⇒ p₂) → (p₂ =[ a ]⇒ p₃) → (p₃ =[ tau ]⇒ p₄) → (p₁ =[ a ]⇒ p₄)
join (tau s₁) (send s₂ t s₃) (tau s₄) = send (concat s₁ s₂) t (concat s₃ s₄)
join (tau s₁) (recv s₂ t s₃) (tau s₄) = recv (concat s₁ s₂) t (concat s₃ s₄)
join (tau s₁) (tau s₂)       (tau s₃) = tau (concat s₁ (concat s₂ s₃))

-- Joins two weak tau transitions
join-tau : (p₁ =[ tau ]⇒ p₂) → (p₂ =[ tau ]⇒ p₃) → (p₁ =[ tau ]⇒ p₃)
join-tau (tau s₁) (tau s₂) = tau (concat s₁ s₂)

-- Maps each transition in a TauSeq
s-map : {f : Proc → Proc} → (g : ∀ {p q} → (p -[ tau ]→ q) → (f p -[ tau ]→ f q))
        → (p -[tau]→* q) → (f p -[tau]→* f q)
s-map {f = f} g self       = self
s-map {f = f} g (cons t s) = cons (g t) (s-map g s)

-- Maps each transition in a WeakTrans
w-map : {f : Proc → Proc} → (g : ∀ {p q a} → (p -[ a ]→ q) → (f p -[ a ]→ f q))
        → (p =[ a ]⇒ q) → (f p =[ a ]⇒ f q)
w-map {f = f} g (send s₁ t s₂) = send (s-map g s₁) (g t) (s-map g s₂)
w-map {f = f} g (recv s₁ t s₂) = recv (s-map g s₁) (g t) (s-map g s₂)
w-map {f = f} g (tau s)        = tau (s-map g s)

-- Like Trans.par-B but for weak transitions
w-par-B : (pl =[ a ]⇒ ql) → (pr =[ flip-act a ]⇒ qr) → (par pl pr =[ tau ]⇒ par ql qr)
w-par-B (send sl₁ tl sl₂) (recv sr₁ tr sr₂) =
  let s₁ = concat (s-map par-L sl₁) (s-map par-R sr₁)
      s₂ = concat (s-map par-L sl₂) (s-map par-R sr₂)
  in tau (concat s₁ (cons (par-B tl tr) s₂))
w-par-B (recv sl₁ tl sl₂) (send sr₁ tr sr₂) =
  let s₁ = concat (s-map par-L sl₁) (s-map par-R sr₁)
      s₂ = concat (s-map par-L sl₂) (s-map par-R sr₂)
  in tau (concat s₁ (cons (par-B tl tr) s₂))
w-par-B (tau sl) (tau sr) = tau (concat (s-map par-L sl) (s-map par-R sr))

-- Like Trans.hide but for weak transitions
w-hide : ∀ {f} → filter-act f a → (p =[ a ]⇒ q) → (hide f p =[ a ]⇒ hide f q)
w-hide z (send s₁ t s₂) = send (s-map (hide tt) s₁) (hide z t) (s-map (hide tt) s₂)
w-hide z (recv s₁ t s₂) = recv (s-map (hide tt) s₁) (hide z t) (s-map (hide tt) s₂)
w-hide z (tau s)        = tau (s-map (hide tt) s)

-- Like Trans.rename but for weak transitions
w-rename : ∀ {f} → (p =[ a ]⇒ q) → (rename f p =[ map-act f a ]⇒ rename f q)
w-rename (send s₁ t s₂) = send (s-map rename s₁) (rename t) (s-map rename s₂)
w-rename (recv s₁ t s₂) = recv (s-map rename s₁) (rename t) (s-map rename s₂)
w-rename (tau s)        = tau (s-map rename s)
