open import Data.Bool
open import Data.Bool.Properties
open import Data.Empty
open import Data.List
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable.Core

module ccs-vp.proc {C N X V : Set} {n-fv : N -> X -> Bool} {_≡?_ : DecidableEquality X} where

FV : Set
FV = X -> Bool

add-fv : X -> FV -> FV
add-fv x fv y with x ≡? y
... | yes x≡y = true
... | no ¬x≡y = fv y

add-fv-respects-≡ : {fv fv' : FV} -> (x y : X) -> fv y ≡ fv' y -> add-fv x fv y ≡ add-fv x fv' y
add-fv-respects-≡ x y eq with x ≡? y
... | yes x≡y = refl
... | no ¬x≡y = eq

add-fv-idempotent : {fv fv' : FV} -> (x y : X) -> add-fv x fv y ≡ fv' y -> add-fv x fv y ≡ add-fv x fv' y
add-fv-idempotent x y eq with x ≡? y
... | yes x≡y = refl
... | no ¬x≡y = eq

add-fv-commutes : {fv fv' : FV} -> (x y z : X) -> (¬ x ≡ y) -> add-fv x fv z ≡ fv' z
               -> add-fv x (add-fv y fv) z ≡ add-fv y fv' z
add-fv-commutes {fv} x y z ¬x≡y eq with x ≡? z
add-fv-commutes {fv} x y z ¬x≡y eq | yes x≡z with y ≡? z
... | yes y≡z = refl
... | no ¬y≡z = eq
add-fv-commutes {fv} x y z ¬x≡y eq | no ¬x≡z with y ≡? z
... | yes y≡z = refl
... | no ¬y≡z = eq

empty-fv : FV
empty-fv _ = false

VEnv : FV -> Set
VEnv fv = (x : X) -> T (fv x) -> V

empty-venv : VEnv empty-fv
empty-venv x ()

eval : {S : Set} -> (VEnv empty-fv -> S) -> S
eval e = e empty-venv

-- A CCS VP Process
data ProcFV (fv : FV) : Set₁ where
  send   : C -> (VEnv fv -> V) -> ProcFV fv -> ProcFV fv
  recv   : C -> (x : X) -> ProcFV (add-fv x fv) -> ProcFV fv
  tau    : ProcFV fv -> ProcFV fv
  par    : ProcFV fv -> ProcFV fv -> ProcFV fv
  indet  : {S : Set} -> (S -> ProcFV fv) -> ProcFV fv
  const  : (n : N) -> (VEnv fv -> VEnv (n-fv n)) -> ProcFV fv
  rename : (C -> C) -> ProcFV fv -> ProcFV fv
  hide   : (C -> Bool) -> ProcFV fv -> ProcFV fv
  if     : (VEnv fv -> Bool) -> ProcFV fv -> ProcFV fv

Proc : Set₁
Proc = ProcFV empty-fv

-- The "desugaring" of the deadlock CCS VP Process
deadlock : {fv : FV} -> ProcFV fv
deadlock = indet ⊥-elim

rebind-venv : {fv fv' : FV} -> ((x : X) -> fv x ≡ fv' x) -> VEnv fv -> VEnv fv'
rebind-venv eq venv' x tfvx rewrite sym (eq x) = venv' x tfvx

rebind-proc : {fv fv' : FV} -> ((x : X) -> fv x ≡ fv' x) -> ProcFV fv' -> ProcFV fv
rebind-proc eq (send c e p) = send c (\ venv -> e (rebind-venv eq venv)) (rebind-proc eq p)
rebind-proc eq (recv c x p) = recv c x (rebind-proc (\ y -> add-fv-respects-≡ x y (eq y)) p)
rebind-proc eq (tau p) = tau (rebind-proc eq p)
rebind-proc eq (par pl pr) = par (rebind-proc eq pl) (rebind-proc eq pr)
rebind-proc eq (indet f) = indet \ s -> rebind-proc eq (f s)
rebind-proc eq (const n nvenv) = const n \ venv -> nvenv (rebind-venv eq venv)
rebind-proc eq (rename f p) = rename f (rebind-proc eq p)
rebind-proc eq (hide f p) = hide f (rebind-proc eq p)
rebind-proc eq (if eb p) = if (\ venv -> eb (rebind-venv eq venv)) (rebind-proc eq p)

module _  {fv fv' : FV} (x : X) (v : V) {eq : (y : X) -> add-fv x fv y ≡ fv' y} where
  bind-venv : VEnv fv -> VEnv fv'
  bind-venv venv y tfvy rewrite sym (eq y) with x ≡? y
  ... | yes x≡y = v
  ... | no ¬x≡y = venv y tfvy

  bind-expr : {S : Set} -> (VEnv fv' -> S) -> (VEnv fv -> S)
  bind-expr e venv = e (bind-venv venv)

bind-proc : {fv fv' : FV} (x : X) -> V -> {eq : (y : X) -> add-fv x fv y ≡ fv' y} -> ProcFV fv' -> ProcFV fv
bind-proc x v {eq} (send c e p) = send c (bind-expr x v {eq} e) (bind-proc x v {eq} p)
bind-proc x v {eq} (recv c y p) with x ≡? y
... | yes refl = recv c y (rebind-proc (\ z -> add-fv-idempotent x z (eq z)) p)
... | no ¬x≡y = recv c y ((bind-proc x v {\ z -> add-fv-commutes x y z ¬x≡y (eq z)} p))
bind-proc x v {eq} (tau p) = tau (bind-proc x v {eq} p)
bind-proc x v {eq} (par pl pr) = par (bind-proc x v {eq} pl) (bind-proc x v {eq} pr)
bind-proc x v {eq} (indet f) = indet \ s -> bind-proc x v {eq} (f s)
bind-proc x v {eq} (const n nvenv) = const n (\ avenv -> nvenv (bind-venv x v {eq} avenv))
bind-proc x v {eq} (rename f p) = rename f (bind-proc x v {eq} p)
bind-proc x v {eq} (hide f p) = hide f (bind-proc x v {eq} p)
bind-proc x v {eq} (if eb p) = if (bind-expr x v {eq} eb) (bind-proc x v {eq} p)

bind-proc' : (x : X) -> V -> ProcFV (add-fv x empty-fv) -> ProcFV empty-fv
bind-proc' x v p = bind-proc x v {\ _ -> refl} p

-- A CCS VP action. This is a bit different than the CCS's Act
-- in that Processes don't contain channel operations (they are codified in different ways)
-- and this is only used in `Trans`.
data Act : Set where
  send : C -> V -> Act
  recv : C -> V -> Act
  tau  : Act

-- Utility functions used in `Trans`
flip-act : Act -> Act
flip-act (send c v) = recv c v
flip-act (recv c v) = send c v
flip-act tau = tau

map-act : (C -> C) -> Act -> Act
map-act f (send c v) = send (f c) v
map-act f (recv c v) = recv (f c) v
map-act f tau = tau

filter-act : (C -> Bool) -> Act -> Bool
filter-act f (send c _) = f c
filter-act f (recv c _) = f c
filter-act f tau = true

PEnv : Set₁
PEnv = (n : N) -> VEnv (n-fv n) -> Proc
 