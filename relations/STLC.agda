module STLC where

open import Data.String
open import Data.Bool hiding (_∧_)
open import Data.List
open import Data.Maybe

data τ : Set where
  bool : τ
  arr : τ -> τ -> τ

data τ-eq : τ -> τ -> Set where
  eqb : τ-eq bool bool
  eqarr : (t1 : τ) -> (t2 : τ) -> (t1' : τ) -> (t2' : τ) -> τ-eq t1 t1' -> τ-eq t2 t2' -> τ-eq (arr t1 t2) (arr t1' t2')

data exp : Set where
  var : String -> exp
  true : exp
  false : exp
  if : exp -> exp -> exp -> exp
  lam : String -> τ -> exp -> exp
  ap : exp -> exp -> exp

data value : exp -> Set where
  val_b1 : value true
  val_b2 : value false
  val_lam : (s : String) -> (t : τ) -> (b : exp) -> value (lam s t b)

data E : Set where
  Eempty : E
  Eif : E -> exp -> exp -> E
  Efun : E -> exp -> E
  Earg : E -> (exp : exp) -> value exp -> E

subst : exp -> String -> exp -> exp
subst e x (var y) = if x == y then e else (var y)
subst e x (if c thn els) = if (subst e x c) (subst e x thn) (subst e x els)
subst e x (lam y t b) = if x == y then (lam y t b) else (lam y t (subst e x b))
subst e x (ap f a) = ap (subst a x f) (subst e x a)
subst _ _ exp = exp

plug : E -> exp -> exp
plug Eempty e = e
plug (Eif ctxt x x₁) e = if (plug ctxt e) x x₁
plug (Efun ctxt x) e = ap (plug ctxt e) x
plug (Earg ctxt exp x) e = ap (plug ctxt exp) e

data red : exp -> exp -> Set where
  red_ift : (e1 : exp) -> (e2 : exp) -> red (if true then e1 else e2) e1
  red_iff : (e1 : exp) -> (e2 : exp) -> red (if false then e1 else e2) e2
  red_app : (x : String) -> (t : τ) -> (b : exp) -> (val : exp) -> value val -> red (ap (lam x t b) val) (subst val x b)
  red_ctxt : (e : exp) -> (e' : exp) -> (ctxt : E) -> red e e' -> red (plug ctxt e) (plug ctxt e')

data environment : Set where
  env : List String -> (String -> Maybe τ) -> environment

empty : environment
empty = env [] (λ _ → nothing)

lookup : environment -> String -> Maybe τ
lookup (env _ f) s = f s

extend : environment -> String -> τ -> environment
extend (env domain f) s t = env (s ∷ domain) (λ x → if (x == s) then just t else f x)

data mteq : Maybe τ -> Maybe τ -> Set where
   meq : (t t' : τ) -> (τ-eq t t') -> mteq (just t) (just t')


data tyderive : environment -> exp -> τ -> Set where
  tylookup : (g : environment) -> (x : String) -> (t t' : τ) -> (mteq (just t') (lookup g x)) -> (τ-eq t' t) -> tyderive g (var x) t
  tytrue : (g : environment) -> tyderive g true bool
  tyfalse : (g : environment) -> tyderive g false bool
  tyif : (g : environment) -> (e e1 e2 : exp) -> (t te1 te2 : τ) -> (tyderive g e t) -> (tyderive g e1 te1) -> (tyderive g e2 te2) -> tyderive g (if e e1 e2) t
  tylam : (g : environment) -> (x : String) -> (t1 t2 : τ) -> (e : exp) -> (tyderive (extend g x t1) e t2) -> tyderive g (lam x t1 e) (arr t1 t2)
  tyap : (g : environment) -> (e1 e2 : exp) -> (t1 t2 : τ) -> (tyderive g e1 (arr t1 t2)) -> (tyderive g e2 t1) -> tyderive g (ap e1 e2) t2

data red-star : exp -> exp -> Set where
  star-refl : (e : exp) -> red-star e e
  star-trans : (e1 e2 e3 : exp) -> red e1 e2 -> red-star e2 e3 -> red-star e1 e3

data ∃ {D : Set} (φ : D -> Set) : Set where
  ∃-intro : (x : D) → φ x → ∃ φ

∃-elim : {D : Set} {φ : D -> Set} -> {ψ : Set}
  -> ((x : D) -> φ x -> ψ)
  -> ∃ φ -> ψ
∃-elim d (∃-intro x p) = d x p


data _∧_ (φ ψ : Set) : Set where
  ∧-intro : φ → ψ → φ ∧ ψ

∧-elim₀ : {φ ψ : Set} → φ ∧ ψ → φ
∧-elim₀ (∧-intro a b) = a

∧-elim₁ : {φ ψ : Set} → φ ∧ ψ → ψ
∧-elim₁ (∧-intro a b) = b

-- NOTE(dbp 2015-06-23): Not sure how to represent empty Γ, when Γ is a function.
SN : τ -> exp -> Set
SN bool e = (tyderive empty e bool) ∧ (∃ (λ v -> value v ∧ red-star e v))
SN (arr t1 t2) e = (tyderive empty e (arr t1 t2)) ∧ ((∃ (λ v -> value v ∧ red-star e v)) ∧ ((e' : exp) -> SN t1 e' -> SN t2 (ap e e')))

proofB : (e : exp) -> (t : τ) -> SN t e -> ∃ (λ v -> value v ∧ red-star e v)
proofB e bool (∧-intro _ (∃-intro v p)) = ∃-intro v p
proofB e (arr t t₁) (∧-intro _ (∧-intro (∃-intro v p) _)) = ∃-intro v p

proofA : (e : exp) -> (t : τ) -> tyderive empty e t -> SN t e
proofA e t tyd = {!!}
