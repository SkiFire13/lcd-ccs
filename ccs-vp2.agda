open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

module ccs-vp2 (C N X V : Set) {_==_ : X -> X -> Bool} where

VarSet = X -> Set

Env : VarSet -> Set
Env bv = (x : X) -> {_ : bv x} -> V

VExpr : VarSet -> Set
VExpr bv = Env bv -> V

BExpr : VarSet -> Set
BExpr bv = Env bv -> Bool

empty-bv : VarSet
empty-bv x = ⊥

add-bv : X -> VarSet -> VarSet
add-bv x bv y = if x == y then ⊤ else bv y

data Prog : (bv : VarSet) -> Set₁ where
  chan-send : { bv : _ } -> C -> VExpr bv -> Prog bv -> Prog bv
  chan-recv : { bv : _ } -> C -> (x : X) -> Prog (add-bv x bv) -> Prog bv
  chan-tau  : { bv : _ } -> Prog bv -> Prog bv
  par       : { bv : _ } -> Prog bv -> Prog bv -> Prog bv
  indet     : { bv : _ } -> {S : Set} -> (S -> Prog bv) -> Prog bv
  const     : N -> Prog empty-bv
  rename    : { bv : _ } -> (C -> C) -> Prog bv -> Prog bv
  hide      : { bv : _ } -> (C -> Set) -> Prog bv -> Prog bv
  if        : { bv : _ } -> BExpr bv -> Prog bv -> Prog bv

deadlock : {bv : VarSet} -> Prog bv
deadlock = indet ⊥-elim

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

filter-reduc-op : (C -> Set) -> ReducOp -> Set
filter-reduc-op f (send c _) = f c
filter-reduc-op f (recv c _) = f c
filter-reduc-op f tau = ⊤

variable
  nbv : N -> VarSet
  F : (n : N) -> Prog (nbv n)

data Reduces : (bv1 : VarSet) -> Prog bv1 -> ReducOp -> (bv2 : VarSet) -> Prog bv2 -> Set₁ where

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
  