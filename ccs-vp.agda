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

-- A reduction operation. This is a bit different than the CCS's Act 
-- in that Processes don't contain channel operations (they are codified in different ways)
-- and this is only used in `Reduc`.
data Act : Set where
  send : C -> V -> Act
  recv : C -> V -> Act
  tau  : Act

-- Utility functions used in `Reduc`
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
PEnv = (n : N) -> ((x : X) -> {_ : T (n-fv n x)} -> V) -> Proc

-- A relation of reduction between two CCS-VP processes with a reduction operation.
-- It is also parameterized over the process environment (`penv`), that is the
-- mapping from the name of constants to their process, given the values of the
-- variables the constant will try to bind.
-- (For technical reasons this can't be included in the process type itself)
data Reduc {penv : PEnv} : Proc -> Act -> Proc -> Set₁ where
  chan-send : forall {c v p}
              -> Reduc (chan-send c v p) (send c v) p
  chan-recv : forall {c v f}
              -> Reduc (chan-recv c f) (recv c v) (f v)
  chan-tau  : forall {p}
              -> Reduc (chan-tau p) tau p
  par-L     : forall {c pl pr p'}
              -> Reduc {penv} pl c p'
              -> Reduc (par pl pr) c (par p' pr)
  par-R     : forall {c pl pr p'}
              -> Reduc {penv} pr c p'
              -> Reduc (par pl pr) c (par pl p')
  par-B     : forall {c pl pr pl' pr'}
              -> Reduc {penv} pl c pl'
              -> Reduc {penv} pr (flip-act c) pr'
              -> Reduc (par pl pr) tau (par pl' pr')
  indet     : forall {c q S f}
              -> {s : S}
              -> Reduc {penv} (f s) c q
              -> Reduc (indet f) c q
  const     : forall {c p n f}
              -> Reduc {penv} (penv n f) c p
              -> Reduc (const n f) c p
  rename    : forall {c p q r}
              -> Reduc {penv} p c q
              -> Reduc (rename r p) (map-act r c) (rename r q)
  hide      : forall {c p q f}
              -> {z : T (filter-act f c)}
              -> Reduc {penv} p c q
              -> Reduc (hide f p) c (hide f q)
  if        : forall {c p q}
              -> Reduc {penv} p c q
              -> Reduc (if true p) c q
