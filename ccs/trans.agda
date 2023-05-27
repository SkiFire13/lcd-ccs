import ccs.proc

module ccs.trans (C N : Set) (penv : ccs.proc.PEnv C N) where

open import ccs.proc C N

private
  variable
    p q p' : Proc
    pl pr pl' pr' : Proc
    a : Act
    n : N

-- A (strong) transition between two CCS processes through an action.
data _-[_]→_ : Proc → Act → Proc → Set₁ where
  chan    : chan a p -[ a ]→ p
  par-L   : (pl -[ a ]→ p') → (par pl pr -[ a ]→ par p' pr)
  par-R   : (pr -[ a ]→ p') → (par pl pr -[ a ]→ par pl p')
  par-B   : (pl -[ a ]→ pl') → (pr -[ flip-act a ]→ pr') → (par pl pr -[ τ ]→ par pl' pr')
  indet   : ∀ {S f} (s : S) → (f s -[ a ]→ q) → (indet f -[ a ]→ q)
  const   : (penv n -[ a ]→ p) → (const n -[ a ]→ p)
  rename  : ∀ {f} → (p -[ a ]→ q) → (rename f p -[ map-act f a ]→ rename f q)
  hide    : ∀ {f} → filter-act f a → (p -[ a ]→ q) → (hide f p -[ a ]→ hide f q)
