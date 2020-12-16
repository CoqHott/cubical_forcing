{-# OPTIONS --cubical #-}

-- Definition of Identity types and definitions of J,
-- funExt, univalence and propositional truncation
-- using Id instead of Path

open import Cubical.Foundations.Id public
open import Cubical.Data.Bool public

variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

etaBool : (a : Bool) → a ≡ (if a then true else false)
etaBool true = refl
etaBool false = refl

test : (λ (b : Bool) → b) ≡ (λ (b : Bool) → if b then true else false)
test = funExt (λ a → etaBool a)

-- non-standard boolean using Id

std-bool : Bool
std-bool = transport (λ f → Bool) test true

data eq {A : Type ℓ} (x : A) : A → Type ℓ where
  eq-refl : eq x x 

path-of-eq : {A : Type ℓ} {x y : A} → eq x y → Path A x y 
path-of-eq {ℓ} {A} {x} {.x} eq-refl = reflPath

eq-of-path : {A : Type ℓ} {x y : A} → Path A x y → eq x y
eq-of-path {ℓ} {A} {x} {y} = JPath (λ y _ → eq x y) eq-refl

etaBool' : (a : Bool) → eq a (if a then true else false)
etaBool' true = eq-refl
etaBool' false = eq-refl

funext : {A : Set ℓ} {B : A → Set ℓ₁} {f g : (a : A) → B a} →
          ((a : A) → eq (f a) (g a)) → eq f g 
funext {ℓ} {ℓ₁} {A} {B} {f} {g} e = eq-of-path (funExtPath (λ (a : A) → path-of-eq (e a)))

test' : eq (λ (b : Bool) → b) (λ (b : Bool) → if b then true else false)
test' = funext (λ a → etaBool' a)

transportEq : {A : Type ℓ} (P : A → Type ℓ₁) (x : A) (t : P x) (y : A) (e : eq x y) → P y
transportEq P x t y eq-refl = t

non-std-bool : Bool
non-std-bool = transportEq (λ f → Bool) _ true _ test' 
