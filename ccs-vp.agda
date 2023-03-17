module ccs-vp (C N X E V : Set) where

open import Data.Unit
open import Data.Empty
open import Data.Maybe
open import Relation.Binary.PropositionalEquality

data ChanOp : Set where
  send : C -> E -> ChanOp
  recv : C -> X -> ChanOp
  tau  : ChanOp

data Prog : Set₁ where
  chan    : ChanOp -> Prog -> Prog
  par     : Prog -> Prog -> Prog
  indet   : {S : Set} -> (S -> Prog) -> Prog
  const   : N -> E -> Prog
  rename  : (C -> C) -> Prog -> Prog
  hide    : (C -> Set) -> Prog -> Prog
  if      : E -> (E -> Set) -> Prog -> Prog

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
  F : N -> Prog
  R : X -> V -> E -> E
  Q : E -> Maybe V

data Reduces : Prog -> ReducOp -> Prog -> Set₁ where
  chan-send : forall {c p e v} {_ : Q e ≡ just v} -> Reduces (chan (send c e) p) (send c v) p
  chan-recv : forall {c p x v} -> Reduces (chan (recv c x) p) (recv c v) p -- TODO: remap p
  chan-tau  : forall {p} -> Reduces (chan tau p) tau p
  par-L     : forall {c pl pr p'} -> Reduces pl c p' -> Reduces (par pl pr) c (par p' pr)
  par-R     : forall {c pl pr p'} -> Reduces pr c p' -> Reduces (par pl pr) c (par pl p')
  par-B     : forall {c pl pr pl' pr'} -> Reduces pl c pl' -> Reduces pr (flip-reduc-op c) pr'
              -> Reduces (par pl pr) tau (par pl' pr')
  indet     : forall {c q S f} {s : S} -> Reduces (f s) c q -> Reduces (indet f) c q
  const     : forall {c p n e v} {_ : Q e ≡ just v} -> Reduces (F n) c p -> Reduces (const n e) c p -- TODO: remap (F n)
  rename    : forall {c p q r} -> Reduces p c q -> Reduces (rename r p) (map-reduc-op r c) (rename r q)
  hide      : forall {c p q f} {_ : filter-reduc-op f c} -> Reduces p c q -> Reduces (hide f p) c (hide f q)
  if        : forall {c p q e f} {_ : f e} -> Reduces p c q -> Reduces (if e f p) c q
