open import Data.Bool
open import Data.Empty

module ccs-vp {C N X V : Set} {n-fv : N -> X -> Bool} where

data Prog : Set₁ where
  chan-send : C -> V -> Prog -> Prog
  chan-recv : C -> (V -> Prog) -> Prog
  chan-tau  : Prog -> Prog
  par       : Prog -> Prog -> Prog
  indet     : {S : Set} -> (S -> Prog) -> Prog
  const     : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> Prog
  rename    : (C -> C) -> Prog -> Prog
  hide      : (C -> Bool) -> Prog -> Prog
  if        : Bool -> Prog -> Prog

deadlock : Prog
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

filter-reduc-op : (C -> Bool) -> ReducOp -> Bool
filter-reduc-op f (send c _) = f c
filter-reduc-op f (recv c _) = f c
filter-reduc-op f tau = true

variable
  penv : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> Prog

data Reduces : Prog -> ReducOp -> Prog -> Set₁ where
  chan-send : forall {c v p} -> Reduces (chan-send c v p) (send c v) p
  chan-recv : forall {c v f} -> Reduces (chan-recv c f) (recv c v) (f v)
  chan-tau  : forall {p} -> Reduces (chan-tau p) tau p
  par-L     : forall {c pl pr p'} -> Reduces pl c p' -> Reduces (par pl pr) c (par p' pr)
  par-R     : forall {c pl pr p'} -> Reduces pr c p' -> Reduces (par pl pr) c (par pl p')
  par-B     : forall {c pl pr pl' pr'} -> Reduces pl c pl' -> Reduces pr (flip-reduc-op c) pr'
              -> Reduces (par pl pr) tau (par pl' pr')
  indet     : forall {c q S f} {s : S} -> Reduces (f s) c q -> Reduces (indet f) c q
  const     : forall {c p n f} -> Reduces (penv n f) c p -> Reduces (const n f) c p
  rename    : forall {c p q r} -> Reduces p c q -> Reduces (rename r p) (map-reduc-op r c) (rename r q)
  hide      : forall {c p q f} {z : T (filter-reduc-op f c)} -> Reduces p c q -> Reduces (hide f p) c (hide f q)
  if        : forall {c p q} -> Reduces p c q -> Reduces (if true p) c q
