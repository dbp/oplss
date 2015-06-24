------------------------------------------------------------------------
-- 5. Martin-Löf type theory
------------------------------------------------------------------------

-- We present the intensional monomorphic version of Martin-Löf type theory from 1986,
-- see Nordström, Petersson, and Smith 1989. (It is not exactly the same theory
-- since Agda has (x : A) -> B : Set provided A : Set, B : (x : A) -> Set,
-- whereas (x : A) -> B in Martin-Löf type theory is only a type.)
--
module MLTT.MLTT where

-- generalization of Curry-Howard encoding of predicate logic

data N₀ : Set where

R₀ : {C : N₀ -> Set}
  -> (c : N₀)
  -> C c
R₀ ()

Rpp : (C : Set) -> (c : N₀) -> C
Rpp _ ()

data  N₁ : Set where
  0₁ : N₁

R₁ : {C :  N₁ -> Set}
  → C 0₁
  → (c :  N₁)
  → C c
R₁ d 0₁ = d

data N₂ : Set where
  1₁ : N₂
  1₂ : N₂

R₂ : {C :  N₂ -> Set}
  → C 1₁
  → C 1₂
  → (c :  N₂)
  → C c
R₂ d e 1₁ = d
R₂ d e 1₂ = e


data _+_ (A B : Set) : Set where
  i : A → A + B
  j : B → A + B

D :  {A B : Set}
  → {C : A + B → Set}
  → ((a : A) → C (i a))
  → ((b : B) → C (j b))
  → (c : A + B)
  → C c
D d e (i a) = d a
D d e (j b) = e b

data _+_+_ (A B C : Set) : Set where
  k : A → A + B + C
  l : B → A + B + C
  m : C → A + B + C

Dpp : {A B C : Set}
   → {P : A + B + C → Set}
   → ((a : A) → P (k a))
   → ((b : B) → P (l b))
   → ((c : C) → P (m c))
   → (d : A + B + C)
   → P d
Dpp d e f (k a) = d a
Dpp d e f (l b) = e b
Dpp d e f (m c) = f c

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

syntax Σ A (λ x → B) = Σ[ x ∈ A ] B
-- syntax Σ A (λ x → B) = A ■ x ★ B

-- E' : {A : Set} → {B : Set}
   -- → (f : A ■ x ★ B)
   -- → A
-- E' (a , _) = a

E : {A : Set}
  → {B : A → Set}
  → {C : Σ A B → Set}
  → ((x : A) → (y : B x) → C (x , y))
  → (z : Σ A B)
  → C z
E d (x , y) = d x y

fst : {A : Set} → {B : A → Set} → Σ A B → A
fst (a , b) = a

snd : {A : Set} → {B : A → Set} → (c : Σ A B) → B (fst c)
snd (a , b) = b


-- E' : {A : Set}
--   → {B : A → Set}
--   → {C : Σ A B → Set}
--   → ((x : A) → (y : B x) → C (x , y))
--   → (z : Σ A B)
--   → C z
-- E' {C = C} d s = {!!} where
--   notgood : C ((fst s) , (snd s))
--   notgood = d (fst s) (snd s)


data «_*_« (A B : Set) : Set where
  _ℷ_ : A → B → « A * B «

fst' : {A B : Set} → « A * B « → A
fst' (a ℷ _) = a

snd' : {A B : Set} → « A * B « → B
snd' (_ ℷ b) = b

-- E'' : {A B : Set}
--   → {C : « A * B « → Set}
--   → ((x : A) → (y : B) → C (x ℷ y))
--   → (z : « A * B «)
--   → C z
-- E'' {C = C} f c = {!!} where
--   notgood : C ((fst' c) ℷ (snd' c))
--   notgood = f (fst' c) (snd' c)

-- in intensional type theory E (split) is not derivable from the projections,
-- hence it is taken as a primitive

data Π (A : Set) (B : A → Set) : Set where
  Λ : ((a : A) → B a) → Π A B

syntax Π A (λ x → B) = Π[ x ∈ A ] B

F :  {A : Set}
  → {B : A → Set}
  → {C : Π A B → Set}
  → ((b : (x : A) → B x) → C (Λ b))
  → (z : Π A B)
  → C z
F d (Λ b) = d b

-- in intensional type theory F (funsplit) is more general than application and -- taken as a primitive

-- In the Agda version of Martin-Löf type theory, the framework function
-- space (x : A) → B x more or less replaces Π A B.

data I (A : Set) (a : A) : A → Set where
  r : I A a a

J : {A : Set}
  → {a : A}
  → (C : (y : A) → I A a y → Set)
  → C a r
  → (b : A)
  → (c : I A a b)
  → C b c
J C d b r = d

-- Agda's .-notation

data N : Set where
  O : N
  s : N → N

R : {C : N → Set}
 → C O
 → ((n : N) → C n → C (s n))
 → (c : N)
 → C c
R d e O     = d
R d e (s n) = e n (R d e n)

-- added in Martin-Löf 1979 (cf Scott 1970)
-- W-type: type of well-founded trees
--         generalized inductive definition
--         type of trees with arbitrarily varied branching
-- A - indexing type
-- ex: 2-3 trees. A = N₃= N₁+ N₁+ N₁(leaf, 2-children, 3-children).
--                B 0₃= N₀
--                B 1₃= N₁
--                B 2₃= N
-- encoding any inductive type with W-type requires extensionality.
--
-- essentially the form of any inductive type is like a W-type.
--
-- general shape of a generalized inductive type:
-- data Ind : Set where
-- C₁: (x:A) (side cond.) → Ind (inductive argument) ... → Ind
-- for inductive types, each premise is either side condition or
-- inductive premise.
-- generally, Ind could be (A x → ... → B x → Ind)
--
-- generalize to inductive family:
-- data Ind : ... → I (index set) → ... Set where
-- as above, but Ind needs arguments.
-- ** all inductive (-recursive) definitions can have arbitrary
--    parameters **.
--
-- Example: let B = const Bool. Then b is two trees, b true and b false,
-- so it's a binary tree.
data W (A : Set) (B : A → Set) : Set where
  sup : (a : A)
     → (b : B a → W A B)
     → W A B

wrec : {A : Set}
    → {B : A → Set}
    → {C : W A B → Set}
    → ((a : A) → (b : B a → W A B) → ((x : B a) → C (b x)) → C (sup a b))
    → (c : W A B)
    → C c
wrec {C = C} d (sup a b) = d a b (λ x → wrec {C = C} d (b x))

-- a universe a la Tarski introduced in Martin-Löf 1984

-- induction recursion: usually you first define type
-- inductively. once you know how it's generated, you can define
-- functions by structural recursion (expressed by elimintation
-- principle - pattern matching in agda).

-- with induction recursion, it is possible to let the function
-- that you define by structural recursion to participate in
-- definition of inductive datatype.
--
-- relatively minor extension of regular inductive data types.
mutual
  data U : Set where
     n₀ : U
     n₁ : U
     _⊕_ : U → U → U
     σ : (a : U) → (T a → U) → U
     π : (a : U) → (T a → U) → U
     n : U
     w : (a : U) → (T a → U) → U
     i : (a : U) → T a → T a → U
-- T should return something that was a proper type
-- 'before U was born'
  T : U → Set
  T n₀        = N₀
  T n₁        = N₁
  T (a ⊕ b)   = T a + T b
  T (σ a b)   = Σ (T a) (λ x → T (b x))
  T (π a b)   = Π (T a) (λ x → T (b x))
  T n         = N
  T (w a b)   = W (T a) (λ x → T (b x))
  T (i a b c) = I (T a) b c

-- extensional type theory. should not be forgotten.
