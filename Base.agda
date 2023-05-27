open import Level using (_⊔_)

data Bool : Set where
  true false : Bool

if_then_else_ : ∀ {l} {S : Set l} → Bool → S → S → S
if true  then s else _ = s
if false then _ else s = s

Filter : Set → Set₁
Filter S = S → Set

record T : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ∀ {l} {S : Set l} → ⊥ → S
⊥-elim ()

¬_ : ∀ {l} → Set l → Set l
¬_ S = S → ⊥
infix 3 ¬_

data _≡_ {l} {S : Set l} : S → S → Set l where
  refl : {s : S} → s ≡ s

{-# BUILTIN EQUALITY _≡_ #-}

module _ {l} {A B : Set l} (f : A → B) (x : A) where
  record Reveal (y : B) : Set l where
    constructor [_]
    field eq : f x ≡ y
  
  inspect : Reveal (f x)
  inspect = [ refl ]

record ∃ {a b} {A : Set a} (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fst : A
    snd : B fst

infix 2 ∃
syntax ∃ (λ x → B) = ∃[ x ] B

infixr 4 _,_
infixr 2 _×_

_×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (a ⊔ b)
A × B = ∃ {A = A} (λ _ → B)
