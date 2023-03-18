open import Data.Bool
open import Data.Bool.Properties
open import Data.Empty
open import Data.Unit

open import Agda.Builtin.Equality
open import Relation.Binary.Definitions
open import Relation.Nullary.Decidable

module ccs-vp2 (C N X V : Set) {eqX : DecidableEquality X} where

_==_ = \ x y -> isYes (eqX x y)

VarSubset = X -> Bool

Env : VarSubset -> Set
Env fv = (x : X) -> {_ : T (fv x)} -> V

VExpr : VarSubset -> Set
VExpr fv = Env fv -> V

BExpr : VarSubset -> Set
BExpr fv = Env fv -> Bool

empty-fv : VarSubset
empty-fv x = false

add-fv : X -> VarSubset -> VarSubset
add-fv x fv = \ y -> if x == y then true else fv y

add-env : {fv : _} -> (x : X) -> V -> Env fv -> Env (add-fv x fv)
add-env {fv} x v env y {p} with x == y
... | true = v
... | false = (env y {p})

variable
  n-fv : N -> VarSubset

data Prog (fv : VarSubset) : Set₁ where
  chan-send : C -> VExpr fv -> Prog fv -> Prog fv
  chan-recv : C -> (x : X) -> Prog (add-fv x fv) -> Prog fv
  chan-tau  : Prog fv -> Prog fv
  par       : Prog fv -> Prog fv -> Prog fv
  indet     : {S : Set} -> (S -> Prog fv) -> Prog fv
  const     : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> VExpr fv) -> Prog fv
  rename    : (C -> C) -> Prog fv -> Prog fv
  hide      : (C -> Set) -> Prog fv -> Prog fv
  if        : BExpr fv -> Prog fv -> Prog fv

deadlock : {fv : VarSubset} -> Prog fv
deadlock = indet ⊥-elim

-- upcast-prog : {fv1 : VarSubset} {fv2 : VarSubset} {_ : (v : V) -> T (fv2 v) -> T (fv1 v)} -> Prog fv1 -> Prog fv2

data ReducOp : Set where
  send : C -> V -> ReducOp
  recv : C -> V -> ReducOp
  tau  : ReducOp

flip-reduc-op : ReducOp -> ReducOp
flip-reduc-op (send c v) = recv c v
flip-reduc-op (recv c v) = send c v
flip-reduc-op tau = tau

map-reduc-op : (C -> C) -> ReducOp -> ReducOp
map-reduc-op f (send c v) = send (f c) v
map-reduc-op f (recv c v) = recv (f c) v
map-reduc-op f tau = tau

filter-reduc-op : (C -> Bool) -> ReducOp -> Bool
filter-reduc-op f (send c _) = f c
filter-reduc-op f (recv c _) = f c
filter-reduc-op f tau = true

variable
  n-to-prog : (n : N) -> Prog (n-fv n)

record ProgW : Set₁ where
  constructor progw
  field
    fv   : VarSubset
    env  : Env fv
    prog : Prog fv

data Reduces : ProgW -> ReducOp -> ProgW -> Set₁ where
  chan-send : forall {fv env c e p} -> Reduces (progw fv env (chan-send c e p)) (send c (e env)) (progw fv env p)
  chan-recv : forall {fv env x p c v} -> Reduces (progw fv env (chan-recv c x p)) (recv c v) (progw (add-fv x fv) (add-env x v env) p)
  chan-tau  : forall {fv env p} -> Reduces (progw fv env (chan-tau p)) tau (progw fv env p)
  -- par-L     : forall {fv env c pl pr p'} -> Reduces (progw fv1 env pl) c (progw fv2 p' -> Reduces (progw fv env (par pl pr)) c (progw fv env (par p' pr))

  -- TODO: Problem: par progs have different environments -> need to put them inside Prog

-- data Reduces : Prog -> ReducOp -> Prog -> Set₁ where
--   chan-send : forall {c p e v} {_ : Q e ≡ just v} -> Reduces (chan (send c e) p) (send c v) p
--   chan-recv : forall {c p x v} -> Reduces (chan (recv c x) p) (recv c v) p -- TODO: remap p
--   chan-tau  : forall {p} -> Reduces (chan tau p) tau p
--   par-L     : forall {c pl pr p'} -> Reduces pl c p' -> Reduces (par pl pr) c (par p' pr)
--   par-R     : forall {c pl pr p'} -> Reduces pr c p' -> Reduces (par pl pr) c (par pl p')
--   par-B     : forall {c pl pr pl' pr'} -> Reduces pl c pl' -> Reduces pr (flip-reduc-op c) pr'
--               -> Reduces (par pl pr) tau (par pl' pr')
--   indet     : forall {c q S f} {s : S} -> Reduces (f s) c q -> Reduces (indet f) c q
--   const     : forall {c p n e v} {_ : Q e ≡ just v} -> Reduces (F n) c p -> Reduces (const n e) c p -- TODO: remap (F n)
--   rename    : forall {c p q r} -> Reduces p c q -> Reduces (rename r p) (map-reduc-op r c) (rename r q)
--   hide      : forall {c p q f} {_ : filter-reduc-op f c} -> Reduces p c q -> Reduces (hide f p) c (hide f q)
--   if        : forall {c p q e f} {_ : f e} -> Reduces p c q -> Reduces (if e f p) c q
    