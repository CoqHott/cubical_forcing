{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma

record Con {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,,_
  field
    fstC : A
    sndC : B fstC

open Con public

infixr 4 _,,_

variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

postulate Id : (A : Set ℓ) → A → A → Prop ℓ

postulate Id_refl : {A : Set ℓ} (x : A) → Id A x x

postulate transport : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

postulate transport_refl : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (e : Id A x x) → Id (P x) (transport P x t x e) t

record Box (A : Prop ℓ) : Set ℓ where
  constructor box
  field
    unbox : A

open Box public

inverse : (A : Set ℓ) (x y : A) (p : Id {ℓ} A x y) → Id A y x
inverse A x y p = unbox (transport (λ z → Box (Id A z x)) x (box (Id_refl x)) y p )

postulate Id_Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
                  Id ((a : A) → B a) f g ≡ ((a : A) → Id (B a) (f a) (g a))

{-# REWRITE Id_Pi #-}

postulate Id_Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (p q : Σ A B) → 
                     Id (Σ A B) p q ≡ Con (Id A (fst p) (fst q)) (λ e → Id (B (fst p)) (snd p) ((transport B (fst q) (snd q) (fst p) (inverse A _ _ e))))

{-# REWRITE Id_Sigma #-}

record ⊤ : Prop ℓ where
  constructor tt
  
postulate Id_Box : (A : Prop ℓ) (p q : Box A) → Id (Box A) p q ≡ ⊤

{-# REWRITE Id_Box #-}

record Unit : Set ℓ where
  constructor unit

postulate Id_Unit : (p q : Unit{ℓ}) → Id Unit p q ≡ ⊤

{- # REWRITE Id_Unit # -}

contr_sing : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) →
    Id (Σ A (λ y → Box (Id A x y))) (x , box (Id_refl x)) (y , box p) 
contr_sing A {x} {y} p = p ,, tt

J : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Set ℓ₁) 
    (t : P x (Id_refl x)) (y : A) (e : Id A x y) → P y e
J A x P t y e = transport (λ z → P (fst z) (unbox (snd z))) (x , box (Id_refl x)) t (y , box e) (contr_sing A e)


transport_inv : (X : Set ℓ) (A : X → Set ℓ₁) 
                (x : X) (y : X) (e : Id X x y) (a : A x) →
    Id (A x) a (transport A y (transport A x a y e) x (inverse X x y e))
transport_inv X A x y e a = let e_refl = transport_refl A x a (Id_refl x)
                                e_refl_inv = inverse (A x) ((transport A x a x _)) a e_refl
                            in unbox (J X x ((λ y e → Box (Id (A x) a (transport A y (transport A x a y e) x (inverse X x y e))))) ((transport (λ Z → Box (Id (A x) a (transport A x Z x (Id_refl x)))) a (box e_refl_inv) _ e_refl_inv)) y e)

postulate transport_Pi : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                         (x : X) (f : (a : A x) → B x a) (y : X) (e : Id X x y) →
                         transport (λ x → (a : A x) → B x a) x f y e ≡
                         λ (a' : A y) → let a = transport A y a' x (inverse X x y e)
                                        in transport (λ z → B (fst z) (snd z)) (x , a) (f a) (y , a')
                                                     ( e ,, Id_refl (transport A y a' x (inverse X x y e)) )

{-# REWRITE transport_Pi #-}

funext : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
         Id ((a : A) → B a) f g -> ((a : A) → Id (B a) (f a) (g a))
funext A B f g e = e


postulate transport_Sigma : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                            (x : X) (s : Σ (A x) (B x)) (y : X) (e : Id X x y) →
                            transport (λ z → Σ (A z) (B z)) x s y e ≡
                            let a = fst s
                                b = snd s
                                a' = transport A x a y e
                            in a' , transport (λ z → B (fst z) (snd z)) (x , a) b (y , a') (e ,, transport_inv X A x y e a)

{-# REWRITE transport_Sigma #-}

postulate transport_Unit : (X : Set ℓ)  
                           (x : X) (s : Unit{ℓ₁}) (y : X) (e : Id X x y) →
                           transport (λ x → Unit) x s y e ≡ s

{-# REWRITE transport_Unit #-}


test_J_refl_on_closed_term : (X : Set ℓ) (x : X) →
       transport (λ z → Σ Unit (λ z → Unit)) x (unit {ℓ₁}, unit {ℓ₁}) x (Id_refl x) ≡ (unit , unit)
test_J_refl_on_closed_term X x = refl 
