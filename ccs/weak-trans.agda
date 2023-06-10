{-# OPTIONS --safe #-}

open import Base

import ccs.proc

module ccs.weak-trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.proc C N
open import ccs.trans C N penv

private
  variable
    p q r : Proc
    p₁ p₂ p₃ p₄ : Proc
    pl pr ql qr : Proc
    a : Act
    c : C

-- A (potentially empty) sequence of strong τ transitions
data _-[τ]→*_ : Proc → Proc → Set₁ where
  self : p -[τ]→* p
  cons : (p₁ -[ τ ]→ p₂) → (p₂ -[τ]→* p₃) → (p₁ -[τ]→* p₃)

-- A weak CCS transition
data _=[_]⇒_ : Proc → Act → Proc → Set₁ where
  send : (p₁ -[τ]→* p₂) → (p₂ -[ send c ]→ p₃) → (p₃ -[τ]→* p₄) → (p₁ =[ send c ]⇒ p₄)
  recv : (p₁ -[τ]→* p₂) → (p₂ -[ recv c ]→ p₃) → (p₃ -[τ]→* p₄) → (p₁ =[ recv c ]⇒ p₄)
  τ    : (p₁ -[τ]→* p₂) → (p₁ =[ τ ]⇒ p₂)

-- Convert a normal transition to a weak transition
trans→weak : (p -[ a ]→ q) → (p =[ a ]⇒ q)
trans→weak {a = send c} t = send self t self
trans→weak {a = recv c} t = recv self t self
trans→weak {a = τ}      t = τ (cons t self)

-- Joins two sequences of strong τ transitions
join-s : (p₁ -[τ]→* p₂) → (p₂ -[τ]→* p₃) → (p₁ -[τ]→* p₃)
join-s self        t  = t
join-s (cons t t₁) t₂ = cons t (join-s t₁ t₂)

-- Joins two weak τ transitions
join-t : (p₁ =[ τ ]⇒ p₂) → (p₂ =[ τ ]⇒ p₃) → (p₁ =[ τ ]⇒ p₃)
join-t (τ s₁) (τ s₂) = τ (join-s s₁ s₂)

-- Joins a weak transitions with two weak τ transitions
join-w : (p₁ =[ τ ]⇒ p₂) → (p₂ =[ a ]⇒ p₃) → (p₃ =[ τ ]⇒ p₄) → (p₁ =[ a ]⇒ p₄)
join-w (τ s₁) (send s₂ t s₃) (τ s₄) = send (join-s s₁ s₂) t (join-s s₃ s₄)
join-w (τ s₁) (recv s₂ t s₃) (τ s₄) = recv (join-s s₁ s₂) t (join-s s₃ s₄)
join-w (τ s₁) (τ s₂)         (τ s₃) = τ (join-s s₁ (join-s s₂ s₃))

-- Maps each process and strong transition in a τ sequence
map-s : {f : Proc → Proc} → (g : ∀ {p q} → (p -[ τ ]→ q) → (f p -[ τ ]→ f q))
        → (p -[τ]→* q) → (f p -[τ]→* f q)
map-s g self       = self
map-s g (cons t s) = cons (g t) (map-s g s)

-- Maps each process (with `f`) and strong transition (with `g`) in a weak transition
map-w : {f : Proc → Proc} → (g : ∀ {p q a} → (p -[ a ]→ q) → (f p -[ a ]→ f q))
        → (p =[ a ]⇒ q) → (f p =[ a ]⇒ f q)
map-w g (send s₁ t s₂) = send (map-s g s₁) (g t) (map-s g s₂)
map-w g (recv s₁ t s₂) = recv (map-s g s₁) (g t) (map-s g s₂)
map-w g (τ s)          = τ (map-s g s)

-- Equivalent to the `par-B` constructor of strong transitions for weak transitions
par-B-w : (pl =[ a ]⇒ ql) → (pr =[ flip-act a ]⇒ qr) → (par pl pr =[ τ ]⇒ par ql qr)
par-B-w (send sl₁ tl sl₂) (recv sr₁ tr sr₂) =
  let s₁ = join-s (map-s par-L sl₁) (map-s par-R sr₁)
      s₂ = join-s (map-s par-L sl₂) (map-s par-R sr₂)
  in  τ (join-s s₁ (cons (par-B tl tr) s₂))
par-B-w (recv sl₁ tl sl₂) (send sr₁ tr sr₂) =
  let s₁ = join-s (map-s par-L sl₁) (map-s par-R sr₁)
      s₂ = join-s (map-s par-L sl₂) (map-s par-R sr₂)
  in  τ (join-s s₁ (cons (par-B tl tr) s₂))
par-B-w (τ sl) (τ sr) = τ (join-s (map-s par-L sl) (map-s par-R sr))

-- Equivalent to the `hide` constructor of strong transitions for weak transitions
hide-w : ∀ {f} → filter-act f a → (p =[ a ]⇒ q) → (hide f p =[ a ]⇒ hide f q)
hide-w z (send s₁ t s₂) = send (map-s (hide tt) s₁) (hide z t) (map-s (hide tt) s₂)
hide-w z (recv s₁ t s₂) = recv (map-s (hide tt) s₁) (hide z t) (map-s (hide tt) s₂)
hide-w z (τ s)          = τ (map-s (hide tt) s)

-- Equivalent to the `rename` constructor of strong transitions for weak transitions
rename-w : ∀ {f} → (p =[ a ]⇒ q) → (rename f p =[ map-act f a ]⇒ rename f q)
rename-w (send s₁ t s₂) = send (map-s rename s₁) (rename t) (map-s rename s₂)
rename-w (recv s₁ t s₂) = recv (map-s rename s₁) (rename t) (map-s rename s₂)
rename-w (τ s)          = τ (map-s rename s)
