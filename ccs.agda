module ccs {C N : Set} where
-- C = Channel, N = Name (Constant)

open import Data.Bool
open import Data.Empty

data ChanOp : Set where
  send  : C -> ChanOp
  recv  : C -> ChanOp
  tau   : ChanOp

flip-chan-op : ChanOp -> ChanOp
flip-chan-op (send c) = recv c
flip-chan-op (recv c) = send c
flip-chan-op tau = tau

map-chan-op : (C -> C) -> ChanOp -> ChanOp
map-chan-op f (send c) = send (f c)
map-chan-op f (recv c) = recv (f c)
map-chan-op f tau = tau

filter-chan-op : (C -> Bool) -> ChanOp -> Bool
filter-chan-op f (send c) = f c
filter-chan-op f (recv c) = f c
filter-chan-op f tau = true

data Prog : Set₁ where
  chan    : ChanOp -> Prog -> Prog
  par     : Prog -> Prog -> Prog
  indet   : {S : Set} -> (S -> Prog) -> Prog
  const   : N -> Prog
  rename  : (C -> C) -> Prog -> Prog
  hide    : (C -> Bool) -> Prog -> Prog

deadlock = indet ⊥-elim

open import Relation.Binary.PropositionalEquality

chan-eq-c : forall {c1 c2 p1 p2} -> chan c1 p1 ≡ chan c2 p2 -> c1 ≡ c2
chan-eq-c {c1} {.c1} {p1} {.p1} refl = refl
chan-eq-p : forall {c1 c2 p1 p2} -> chan c1 p1 ≡ chan c2 p2 -> p1 ≡ p2
chan-eq-p {c1} {.c1} {p1} {.p1} refl = refl

par-eq-l : forall {l1 l2 r1 r2} -> par l1 r1 ≡ par l2 r2 -> l1 ≡ l2
par-eq-l {l1} {.l1} {r1} {.r1} refl = refl
par-eq-r : forall {l1 l2 r1 r2} -> par l1 r1 ≡ par l2 r2 -> r1 ≡ r2
par-eq-r {l1} {.l1} {r1} {.r1} refl = refl

indet-eq-S : forall {S1 S2 f1 f2} -> indet {S1} f1 ≡ indet {S2} f2 -> S1 ≡ S2
indet-eq-S {S1} {.S1} {f1} {.f1} refl = refl
indet-eq-f : forall {S f1 f2} -> indet {S} f1 ≡ indet {S} f2 -> f1 ≡ f2
indet-eq-f {S} {f1} {.f1} refl = refl

const-eq-n : forall {n1 n2} -> const n1 ≡ const n2 -> n1 ≡ n2
const-eq-n {n1} {.n1} refl = refl

rename-eq-f : forall {f1 f2 p1 p2} -> rename f1 p1 ≡ rename f2 p2 -> f1 ≡ f2
rename-eq-f {f1} {.f1} {p1} {.p1} refl = refl
rename-eq-p : forall {f1 f2 p1 p2} -> rename f1 p1 ≡ rename f2 p2 -> p1 ≡ p2
rename-eq-p {f1} {.f1} {p1} {.p1} refl = refl

hide-eq-f : forall {f1 f2 p1 p2} -> hide f1 p1 ≡ hide f2 p2 -> f1 ≡ f2
hide-eq-f {f1} {.f1} {p1} {.p1} refl = refl
hide-eq-p : forall {f1 f2 p1 p2} -> hide f1 p1 ≡ hide f2 p2 -> p1 ≡ p2
hide-eq-p {f1} {.f1} {p1} {.p1} refl = refl

data Reduces {penv : N -> Prog} : Prog -> ChanOp -> Prog -> Set₁ where
  chan    : forall {c p} -> Reduces (chan c p) c p
  par-L   : forall {c pl pr p'} -> Reduces {penv} pl c p' -> Reduces (par pl pr) c (par p' pr)
  par-R   : forall {c pl pr p'} -> Reduces {penv} pr c p' -> Reduces (par pl pr) c (par pl p')
  par-B   : forall {c pl pr pl' pr'} -> Reduces {penv} pl c pl' -> Reduces {penv} pr (flip-chan-op c) pr'
            -> Reduces (par pl pr) tau (par pl' pr')
  indet   : forall {S} {c q f} {s : S} -> Reduces {penv} (f s) c q -> Reduces (indet f) c q
  const   : forall {c p n} -> Reduces {penv} (penv n) c p -> Reduces (const n) c p
  rename  : forall {c p q r} -> Reduces {penv} p c q -> Reduces (rename r p) (map-chan-op r c) (rename r q)
  hide    : forall {c p q f} {z : T (filter-chan-op f c)} -> Reduces {penv} p c q -> Reduces (hide f p) c (hide f q)
