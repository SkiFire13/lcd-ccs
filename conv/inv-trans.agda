open import Base

import ccs-vp.proc

module conv.inv-trans (C N V : Set) (Args : N → Set) (penv : ccs-vp.proc.PEnv C N V Args) where

open import conv.proc C N V Args
open import ccs.common Conv-C Conv-N (conv-penv penv) as ccs
open import ccs-vp.common C N V Args penv as vp

-- Prove that the converse of `conv-trans` is not true, that is if there exist
-- a transition between two CCS processes then it's not guaranteed that there
-- exist also a transition between two CCS VP processes that can be converted into them.
¬converse-conv-trans : ¬ (∀ {p₁ a p₂} → (conv-proc p₁ -[ conv-act a ]→ conv-proc p₂) → (p₁ -[ a ]→ᵥ p₂))
¬converse-conv-trans f with () ← f {τ vp.deadlock} {τ} {if true vp.deadlock} chan

-- Prove some lemma about helper functions on channel/actions that are not obvious to Agda.

inv-conv-act : ∀ {ca} → ∃[ a ] (ca ≡ conv-act a)
inv-conv-act {send (conv-c c v)} = send c v , refl
inv-conv-act {recv (conv-c c v)} = recv c v , refl
inv-conv-act {τ}               = τ , refl

inv-flip-eq : ∀ {a} → ccs.flip-act (conv-act a) ≡ conv-act (vp.flip-act a)
inv-flip-eq {send _ _} = refl
inv-flip-eq {recv _ _} = refl
inv-flip-eq {τ}      = refl

inv-rename-eq : ∀ {a a' f} → conv-act a ≡ ccs.map-act (conv-rename f) (conv-act a') → a ≡ vp.map-act f a'
inv-rename-eq {send _ _} {send _ _} refl = refl
inv-rename-eq {recv _ _} {recv _ _} refl = refl
inv-rename-eq {τ}      {τ}      refl = refl

inv-filter-eq : ∀ {a f} → ccs.filter-act (conv-hide f) (conv-act a) ≡ vp.filter-act f a
inv-filter-eq {send c _} = refl
inv-filter-eq {recv c _} = refl
inv-filter-eq {τ}      = refl

-- Prove a less-strong version of the converse of `conv-trans`, that is
-- if the conversion of a CCS VP process to CCS can make a transition to another CCS process
-- then there exists a corresponding transition between the initial CCS VP process
-- and some other CCS VP process that can be converted to the second CCS process.
inv-conv-trans' : ∀ {p₁ a cp₂} → conv-proc p₁ -[ conv-act a ]→ cp₂
                  → ∃[ p₂ ] (cp₂ ≡ conv-proc p₂ × p₁ -[ a ]→ᵥ p₂)
inv-conv-trans' {p₁} {a} t
  with {conv-proc p₁} | {conv-act a} | inspect conv-proc p₁ | inspect conv-act a
inv-conv-trans' {send _ _ p} {send _ _} chan | [ refl ] | [ refl ]
  = p , refl , send
inv-conv-trans' {recv _ f} {recv _ v} (indet _ chan) | [ refl ] | [ refl ]
  = f v , refl , recv
inv-conv-trans' {τ p} {τ} chan | [ refl ] | [ refl ]
  = p , refl , τ
inv-conv-trans' {par pl pr} (par-L tl) | [ refl ] | [ e ]
  with refl ← e
  with pl' , refl , tl' ← inv-conv-trans' tl
  = par pl' pr , refl , par-L tl'
inv-conv-trans' {par pl pr} (par-R tr) | [ refl ] | [ e ]
  with refl ← e
  with pr' , refl , tr' ← inv-conv-trans' tr
  = par pl pr' , refl , par-R tr'
inv-conv-trans' {par pl pr} {τ} (par-B {a = ca} tl tr) | [ refl ] | [ refl ]
  with a , refl ← inv-conv-act {ca}
  rewrite inv-flip-eq {a}
  with pl' , refl , tl' ← inv-conv-trans' tl
  with pr' , refl , tr' ← inv-conv-trans' tr
  = par pl' pr' , refl , par-B tl' tr'
inv-conv-trans' {indet f} {a} (indet s t) | [ refl ] | [ refl ]
  with p' , refl , t' ← inv-conv-trans' t
  = p' , refl , indet s t'
inv-conv-trans' {const n args} (const t) | [ refl ] | [ refl ]
  with p' , refl , t' ← inv-conv-trans' t
  = p' , refl , const t'
inv-conv-trans' {rename f p} (rename {a = ca} t) | [ refl ] | [ e ]
  with a , refl ← inv-conv-act {ca}
  rewrite inv-rename-eq e
  with p' , refl , t' ← inv-conv-trans' t
  = rename f p' , refl , rename t'
inv-conv-trans' {hide f p} {a} (hide z t) | [ refl ] | [ refl ]
  rewrite inv-filter-eq {a} {f}
  with p' , refl , t' ← inv-conv-trans' t = hide f p' , refl , hide z t'
inv-conv-trans' {if false _} (indet () _) | [ refl ] | [ refl ]
inv-conv-trans' {if true p} t | [ refl ] | [ refl ]
  with p' , refl , t' ← inv-conv-trans' t
  = p' , refl , if t'
