open import Data.Bool
open import Data.Empty

-- C = Set of the Channels
-- N = Set of the Names of the constant processes
-- X = Set of the variables
-- V = Set of the values
-- n-fv = A function that returns whether a constant will try to bind a given variable.
--        For example given the constant F(x) = a(x).0:
--        n-fv F x will return True because it will try to bind X
--        n-fv F y will return False because it will not try to bind y
--        Ideally we would track the binded/not binded variables with their values,
--        but that was somewhat problematic.
module ccs-vp {C N X V : Set} {n-fv : N -> X -> Bool} where

-- A CCS-VP Process
data Proc : Set₁ where
  chan-send : C -> V -> Proc -> Proc
  chan-recv : C -> (V -> Proc) -> Proc
  chan-tau  : Proc -> Proc
  par       : Proc -> Proc -> Proc
  indet     : {S : Set} -> (S -> Proc) -> Proc
  const     : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> Proc
  rename    : (C -> C) -> Proc -> Proc
  hide      : (C -> Bool) -> Proc -> Proc
  if        : Bool -> Proc -> Proc

-- The "desugaring" of the deadlock CCS-VP Process
deadlock = indet ⊥-elim

-- A reduction operation. This is a bit different than the CCS's ChanOp 
-- in that Processes don't contain channel operations (they are codified in different ways)
-- and this is only used in `Reduces`.
data ReducOp : Set where
  send : C -> V -> ReducOp
  recv : C -> V -> ReducOp
  tau  : ReducOp

-- Utility functions used in `Reduces`
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

-- A relation of reduction between two CCS-VP processes with a reduction operation.
-- It is also parameterized over the process environment (`penv`), that is the
-- mapping from the name of constants to their process, given the values of the
-- variables the constant will try to bind.
-- (For technical reasons this can't be included in the process type itself)
data Reduces {penv : (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> Proc} : Proc -> ReducOp -> Proc -> Set₁ where
  chan-send : forall {c v p} -> Reduces (chan-send c v p) (send c v) p
  chan-recv : forall {c v f} -> Reduces (chan-recv c f) (recv c v) (f v)
  chan-tau  : forall {p} -> Reduces (chan-tau p) tau p
  par-L     : forall {c pl pr p'} -> Reduces {penv} pl c p' -> Reduces (par pl pr) c (par p' pr)
  par-R     : forall {c pl pr p'} -> Reduces {penv} pr c p' -> Reduces (par pl pr) c (par pl p')
  par-B     : forall {c pl pr pl' pr'} -> Reduces {penv} pl c pl' -> Reduces {penv} pr (flip-reduc-op c) pr'
              -> Reduces (par pl pr) tau (par pl' pr')
  indet     : forall {c q S f} {s : S} -> Reduces {penv} (f s) c q -> Reduces (indet f) c q
  const     : forall {c p n f} -> Reduces {penv} (penv n f) c p -> Reduces (const n f) c p
  rename    : forall {c p q r} -> Reduces {penv} p c q -> Reduces (rename r p) (map-reduc-op r c) (rename r q)
  hide      : forall {c p q f} {z : T (filter-reduc-op f c)} -> Reduces {penv} p c q -> Reduces (hide f p) c (hide f q)
  if        : forall {c p q} -> Reduces {penv} p c q -> Reduces (if true p) c q
