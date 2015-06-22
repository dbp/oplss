module Exercises where

open import MLTT.PropositionalLogic
open import MLTT.PredicateLogic
open import IType.Nat
open import IType.Bool
open import SmallProofs.BoolProofs

_➲_ : Bool → Bool → Bool
true ➲ b = b
false ➲ _ = true


em : (b : Bool) → So (b || (not b))
em true = ⊤-intro
em false = ⊤-intro

dm : (a b : Bool) -> So (not (a && b) <==> ((not a) || (not b)))
dm true true = ⊤-intro
dm true false = ⊤-intro
dm false true = ⊤-intro
dm false false = ⊤-intro

Pred : Nat -> Set
Pred zero = Bool
Pred (succ n) = Bool -> Pred n

taut : (n : Nat) -> Pred n -> Bool
taut zero      P = P
taut (succ n') P = taut n' (P true) || taut n' (P false)


_^_ : Nat -> Nat -> Nat
x ^ 0 = 1
x ^ 1 = x
x ^ (succ n) = x * (x ^ n)

pow : Nat -> Nat -> Nat
pow x y = natrec 1 (λ _ b → b * x) y

band : (a b : Bool) -> So a -> So b -> So (a && b)
band true true ⊤-intro ⊤-intro = ⊤-intro
band _ false _ bot = ⊥-elim bot
band false _ bot _ = ⊥-elim bot

_==_ : Nat -> Nat -> Set
0        == 0        = ⊤
(succ n) == 0        = ⊥
0        == (succ m) = ⊥
(succ n) == (succ m) = n == m

_===_ : Nat -> Nat -> Bool
_===_ = λ x -> natrec (λ y → natrec true (λ _ _ → false) y)
                      (λ x' Px' → λ y → natrec false (λ y' _ → Px' y') y)
                      x


t1 : pow 2 3 == 8
t1 = ⊤-intro

t1-5 : So (not (pow 2 3 === 1))
t1-5 = ⊤-intro

t2 : So (3 === 3)
t2 = ⊤-intro


6↦a : {P : Set} → ¬(¬(¬(P))) → ¬ P
6↦a P = λ p → P (λ p' → p' p)

6↦b : {P Q : Set} → (¬(P ∨ Q) → ¬ P ∧ ¬ Q) ∧ ( ¬ P ∧ ¬ Q → ¬(P ∨ Q))
6↦b = ∧-intro (λ x → ∧-intro (λ y → x (∨-intro₀ y)) (λ y → x (∨-intro₁ y)))
               (λ x → λ y → ∨-elim (λ p → ∧-elim₀ x p) (λ q → ∧-elim₁ x q) y)

6↦c : {D : Set} → {P : Set -> Set} → ∧-intro (¬ (∃ P) ()
6↦c = ?
