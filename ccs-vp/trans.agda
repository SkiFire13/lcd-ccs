open import Base

import ccs-vp.proc

module ccs-vp.trans (C N X V : Set) (n-fv : N → Filter X) (penv : ccs-vp.proc.PEnv C N X V n-fv) where

open import ccs-vp.proc C N X V n-fv

private
  variable
    {p q p'} : Proc
    {pl pr pl' pr'} : Proc
    {a} : Act
    {c} : C
    {n} : N
    {v} : V

-- A transition between two CCS VP processes through an action.
data _-[_]→ᵥ_ : Proc → Act → Proc → Set₁ where
  send   : send c v p -[ send c v ]→ᵥ p
  recv   : ∀ {f} → (recv c f -[ recv c v ]→ᵥ f v)
  tau    : tau p -[ tau ]→ᵥ p
  par-L  : (pl -[ a ]→ᵥ p') → (par pl pr -[ a ]→ᵥ par p' pr)
  par-R  : (pr -[ a ]→ᵥ p') → (par pl pr -[ a ]→ᵥ par pl p')
  par-B  : (pl -[ a ]→ᵥ pl') → (pr -[ flip-act a ]→ᵥ pr') → (par pl pr -[ tau ]→ᵥ par pl' pr')
  indet  : ∀ {S f} {s : S} → (f s -[ a ]→ᵥ q) → (indet f -[ a ]→ᵥ q)
  const  : ∀ {f} → (penv n f -[ a ]→ᵥ p) → (const n f -[ a ]→ᵥ p)
  rename : ∀ {f} → (p -[ a ]→ᵥ q) → (rename f p -[ map-act f a ]→ᵥ rename f q)
  hide   : ∀ {f} → filter-act f a → (p -[ a ]→ᵥ q) → (hide f p -[ a ]→ᵥ hide f q)
  if     : (p -[ a ]→ᵥ q) → (if true p -[ a ]→ᵥ q)
