open import Base

import ccs-vp.proc

module ccs-vp.trans (C N V : Set) (Args : N → Set) (penv : ccs-vp.proc.PEnv C N V Args) where

open import ccs-vp.proc C N V Args

private
  variable
    p q p' : Proc
    pl pr pl' pr' : Proc
    a : Act
    c : C
    n : N
    v : V

-- A (strong) transition between two CCS VP processes through an action.
data _-[_]→ᵥ_ : Proc → Act → Proc → Set₁ where
  send   : send c v p -[ send c v ]→ᵥ p
  recv   : ∀ {f} → (recv c f -[ recv c v ]→ᵥ f v)
  τ      : τ p -[ τ ]→ᵥ p
  par-L  : (pl -[ a ]→ᵥ p') → (par pl pr -[ a ]→ᵥ par p' pr)
  par-R  : (pr -[ a ]→ᵥ p') → (par pl pr -[ a ]→ᵥ par pl p')
  par-B  : (pl -[ a ]→ᵥ pl') → (pr -[ flip-act a ]→ᵥ pr') → (par pl pr -[ τ ]→ᵥ par pl' pr')
  indet  : ∀ {S f} (s : S) → (f s -[ a ]→ᵥ q) → (indet f -[ a ]→ᵥ q)
  const  : ∀ {args} → (penv n args -[ a ]→ᵥ p) → (const n args -[ a ]→ᵥ p)
  rename : ∀ {f} → (p -[ a ]→ᵥ q) → (rename f p -[ map-act f a ]→ᵥ rename f q)
  hide   : ∀ {f} → filter-act f a → (p -[ a ]→ᵥ q) → (hide f p -[ a ]→ᵥ hide f q)
  if     : (p -[ a ]→ᵥ q) → (if true p -[ a ]→ᵥ q)
