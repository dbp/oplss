module LF.Nat where


data Nat : Set where
  zero : Nat
  succ : Nat → Nat
{-# BUILTIN NATURAL Nat #-}

ten : Nat
ten = 10

one = succ zero
two = succ one

pred : Nat → Nat
pred zero = zero
pred (succ n) = n


_+_ : Nat -> Nat -> Nat
m + zero = m
m + succ n = succ (m + n)

_-_ : Nat -> Nat -> Nat
zero - n = zero
succ m - zero = succ m
succ m - succ n = m - n

natrec : {X : Set} → X → (Nat → X → X) → Nat → X
natrec base step zero = base
natrec base step (succ n) = step n (natrec base step n)
