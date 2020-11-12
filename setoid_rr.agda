{-# OPTIONS --rewriting --prop #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

-- sigma type in Prop used to handle telescopes. 

record Tel {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,,_
  field
    fstC : A
    sndC : B fstC

open Tel public

infixr 4 _,,_

variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- axiomatisation of Id, Id_refl, transport and transport_refl (propositionally)

postulate Id : (A : Set ℓ) → A → A → Prop ℓ

postulate Id_refl : {A : Set ℓ} (x : A) → Id A x x

postulate transport : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

postulate transport_refl : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (e : Id A x x) → Id (P x) (transport P x t x e) t

-- a bit of boilerplate to deal with Prop

record ⊤P : Prop ℓ where
  constructor ttP

record Box (A : Prop ℓ) : Set ℓ where
  constructor box
  field
    unbox : A

open Box public

transport_prop : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y
transport_prop {A} P x t y e = unbox (transport (λ z → Box (P z)) x (box t) y e)

inverse : (A : Set ℓ) (x y : A) (p : Id {ℓ} A x y) → Id A y x
inverse A x y p = transport_prop (λ z → Id A z x) x (Id_refl x) y p

-- we now state rewrite rules for the identity type

postulate Id_Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
                  Id ((a : A) → B a) f g ≡ ((a : A) → Id (B a) (f a) (g a))

{-# REWRITE Id_Pi #-}

-- sanity check forr funext

funext : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
         Id ((a : A) → B a) f g -> ((a : A) → Id (B a) (f a) (g a))
funext A B f g e = e


postulate Id_Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (p q : Σ A B) → 
                     Id (Σ A B) p q ≡ Tel (Id A (fst p) (fst q)) (λ e → Id (B (fst p)) (snd p) ((transport B (fst q) (snd q) (fst p) (inverse A _ _ e))))

{-# REWRITE Id_Sigma #-}
  
postulate Id_Box : (A : Prop ℓ) (p q : Box A) → Id (Box A) p q ≡ ⊤P

{-# REWRITE Id_Box #-}

postulate Id_Unit : (p q : ⊤) → Id ⊤ p q ≡ ⊤P

{- # REWRITE Id_Unit # -}

postulate Id_Type_Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                          Id (Set (ℓ ⊔ ℓ₁)) (Σ A B) (Σ A' B') ≡
                          Id (Σ (Set ℓ) (λ A → A → Set ℓ₁)) (A , B) (A' , B')

{-# REWRITE Id_Type_Sigma #-}

postulate Id_Type_Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                       Id (Set (ℓ ⊔ ℓ₁)) ((a : A) → B a) ((a' : A') → B' a') ≡
                       Id (Σ (Set ℓ) (λ A → A → Set ℓ₁)) (A , B) (A' , B')

{-# REWRITE Id_Type_Pi #-}

-- Contractibility of singletons and J can be defined

contr_sing : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) →
    Id (Σ A (λ y → Box (Id A x y))) (x , box (Id_refl x)) (y , box p) 
contr_sing A {x} {y} p = p ,, ttP

J : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Set ℓ₁) 
    (t : P x (Id_refl x)) (y : A) (e : Id A x y) → P y e
J A x P t y e = transport (λ z → P (fst z) (unbox (snd z))) (x , box (Id_refl x)) t (y , box e) (contr_sing A e)

-- tranporting back and forth is the identity

transport_inv : (X : Set ℓ) (A : X → Set ℓ₁) 
                (x : X) (y : X) (e : Id X x y) (a : A x) →
    Id (A x) a (transport A y (transport A x a y e) x (inverse X x y e))
transport_inv X A x y e a = let e_refl = transport_refl A x a (Id_refl x)
                                e_refl_inv = inverse (A x) ((transport A x a x _)) a e_refl
                            in unbox (J X x ((λ y e → Box (Id (A x) a (transport A y (transport A x a y e) x (inverse X x y e))))) ((transport (λ Z → Box (Id (A x) a (transport A x Z x (Id_refl x)))) a (box e_refl_inv) _ e_refl_inv)) y e)

-- we can now state rewrite rules for transports

postulate transport_Pi : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                         (x : X) (f : (a : A x) → B x a) (y : X) (e : Id X x y) →
                         transport (λ x → (a : A x) → B x a) x f y e ≡
                         λ (a' : A y) → let a = transport A y a' x (inverse X x y e)
                                        in transport (λ z → B (fst z) (snd z)) (x , a) (f a) (y , a')
                                                     ( e ,, Id_refl (transport A y a' x (inverse X x y e)) )

{-# REWRITE transport_Pi #-}

postulate transport_Sigma : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                            (x : X) (s : Σ (A x) (B x)) (y : X) (e : Id X x y) →
                            transport (λ z → Σ (A z) (B z)) x s y e ≡
                            let a = fst s
                                b = snd s
                                a' = transport A x a y e
                            in a' , transport (λ z → B (fst z) (snd z)) (x , a) b (y , a') (e ,, transport_inv X A x y e a)

{-# REWRITE transport_Sigma #-}

postulate transport_Unit : (X : Set ℓ)  
                           (x : X) (s : ⊤) (y : X) (e : Id X x y) →
                           transport (λ x → ⊤) x s y e ≡ s

{-# REWRITE transport_Unit #-}

-- transporting over the identity it type casting

postulate cast_Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a) (e : _) →
                    transport (λ T → T) ((a : A) → B a) f ((a' : A') → B' a') e ≡
                    transport (λ X → (x : fst X) → (snd X) x) (A , B) f (A' , B') e

{-# REWRITE cast_Pi #-}

postulate cast_Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (s : Σ A B) (e : _) →
                    transport (λ T → T) (Σ A B) s (Σ A' B') e ≡
                    transport (λ X → Σ (fst X) (snd X)) (A , B) s (A' , B') e

{-# REWRITE cast_Sigma #-}



test_J_refl_on_closed_term : (X : Set ℓ) (x : X) →
       transport (λ z → Σ ⊤ (λ z → ⊤)) x (tt , tt) x (Id_refl x) ≡ (tt , tt)
test_J_refl_on_closed_term X x = refl 
