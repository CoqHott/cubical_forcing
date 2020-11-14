{-# OPTIONS --rewriting --prop --confluence-check #-}

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

data ⊥ : Prop where

record ⊤P : Prop ℓ where
  constructor ttP

record Box (A : Prop ℓ) : Set ℓ where
  constructor box
  field
    unbox : A

open Box public

_×_ : ∀ (A : Prop ℓ) (B : Prop ℓ₁) → Prop (ℓ ⊔ ℓ₁)
A × B = Tel A (λ _ → B)

-- we need this for cumulativity

record i (A : Prop ℓ) : Prop (ℓ ⊔ ℓ₁) where
  constructor inj
  field
    uninj : A

transport_prop : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y
transport_prop {A} P x t y e = unbox (transport (λ z → Box (P z)) x (box t) y e)

inverse : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) → Id A y x
inverse A {x} {y} p = transport_prop (λ z → Id A z x) x (Id_refl x) y p

-- we now state rewrite rules for the identity type

postulate Id_Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
                  Id ((a : A) → B a) f g ≡ ((a : A) → Id (B a) (f a) (g a))

{-# REWRITE Id_Pi #-}

-- rewrite rules on Id_refl are not needed because it is in Prop

refl_Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f : (a : A) → B a) →
          box (Id_refl f) ≡ box (λ a → Id_refl (f a))
refl_Pi A B f = refl

-- sanity check for funext

funext : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
         Id ((a : A) → B a) f g → ((a : A) → Id (B a) (f a) (g a))
funext A B f g e = e


postulate Id_Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (p q : Σ A B) → 
                     Id (Σ A B) p q ≡ Tel (Id A (fst p) (fst q))
                                          (λ e → Id (B (fst p)) (snd p)
                                                                ((transport B (fst q) (snd q) (fst p) (inverse A e))))

{-# REWRITE Id_Sigma #-}

postulate Id_Box : (A : Prop ℓ) (p q : Box A) → Id (Box A) p q ≡ ⊤P

{-# REWRITE Id_Box #-}

postulate Id_Unit : (p q : ⊤) → Id ⊤ p q ≡ ⊤P

{-# REWRITE Id_Unit #-}

Id_list_ : (A : Set ℓ) (l l' : List A) → Prop ℓ
Id_list_ A [] [] = ⊤P
Id_list_ A [] (x ∷ l') = i ⊥
Id_list_ A (x ∷ l) [] = i ⊥
Id_list_ A (x ∷ l) (x₁ ∷ l') = ⊤P

postulate Id_list : (A : Set ℓ) (l l' : List A) → Id (List A) l l' ≡ Id_list_ A l l'

{-# REWRITE Id_list #-}

-- rewrite rules for the identity type on the universe

postulate Id_Type_Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                          Id (Set (ℓ ⊔ ℓ₁)) (Σ A B) (Σ A' B') ≡
                          Id (Σ (Set ℓ) (λ A → A → Set ℓ₁)) (A , B) (A' , B')

{-# REWRITE Id_Type_Sigma #-}

postulate Id_Type_Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                       Id (Set (ℓ ⊔ ℓ₁)) ((a : A) → B a) ((a' : A') → B' a') ≡
                       Id (Σ (Set ℓ) (λ A → A → Set ℓ₁)) (A , B) (A' , B')

{-# REWRITE Id_Type_Pi #-}

postulate Id_Type_List : (A A' : Set ℓ) →
                       Id (Set ℓ) (List A) (List A') ≡
                       Id (Set ℓ) A A'

{-# REWRITE Id_Type_List #-}

-- rewrite rules for the identity type on Prop : Prop ext modulo cumul 

postulate Id_prop : (P Q : Prop ℓ) → Id (Prop ℓ) P Q ≡ i (P → Q) × (Q → P)

{-# REWRITE Id_prop #-}

-- Contractibility of singletons and J can be defined

contr_sing : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) →
    Id (Σ A (λ y → Box (Id A x y))) (x , box (Id_refl x)) (y , box p) 
contr_sing A {x} {y} p = p ,, ttP

J : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Set ℓ₁) 
    (t : P x (Id_refl x)) (y : A) (e : Id A x y) → P y e
J A x P t y e = transport (λ z → P (fst z) (unbox (snd z))) (x , box (Id_refl x)) t (y , box e) (contr_sing A e)

J_prop : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Prop ℓ₁) 
    (t : P x (Id_refl x)) (y : A) (e : Id A x y) → P y e
J_prop A x P t y e = transport_prop (λ z → P (fst z) (unbox (snd z))) (x , box (Id_refl x)) t (y , box e) (contr_sing A e)

-- tranporting back and forth is the identity

transport_inv : (X : Set ℓ) (A : X → Set ℓ₁) 
                (x : X) (y : X) (e : Id X x y) (a : A x) →
    Id (A x) a (transport A y (transport A x a y e) x (inverse X e))
transport_inv X A x y e a = let e_refl = transport_refl A x a (Id_refl x)
                                e_refl_inv = inverse (A x) e_refl
                            in J_prop X x (λ y e → Id (A x) a (transport A y (transport A x a y e) x (inverse X e)))
                                      (transport_prop (λ Z → Id (A x) a (transport A x Z x (Id_refl x))) a e_refl_inv _ e_refl_inv) y e

-- we can now state rewrite rules for transports

postulate transport_Pi : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                         (x : X) (f : (a : A x) → B x a) (y : X) (e : Id X x y) →
                         transport (λ x → (a : A x) → B x a) x f y e ≡
                         λ (a' : A y) → let a = transport A y a' x (inverse X e)
                                        in transport (λ z → B (fst z) (snd z)) (x , a) (f a) (y , a')
                                                     ( e ,, Id_refl (transport A y a' x (inverse X e)) )

{-# REWRITE transport_Pi #-}

postulate transport_Sigma : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                            (x : X) (s : Σ (A x) (B x)) (y : X) (e : Id X x y) →
                            transport (λ z → Σ (A z) (B z)) x s y e ≡
                            let a = fst s
                                b = snd s
                                a' = transport A x a y e
                            in a' , transport (λ z → B (fst z) (snd z)) (x , a) b (y , a') (e ,, transport_inv X A x y e a)

{-# REWRITE transport_Sigma #-}

postulate transport_Unit : (X : Set ℓ) (x : X) (s : ⊤) (y : X) (e : Id X x y) →
                           transport (λ x → ⊤) x s y e ≡ s

{-# REWRITE transport_Unit #-}

transport_List_ : (X : Set ℓ) (A : X → Set ℓ₁) (x : X) (l : List (A x)) (y : X) (e : Id X x y) → List (A y)
transport_List_ X A x [] y e = []
transport_List_ X A x (a ∷ l) y e = (transport A x a y e) ∷ (transport (λ x → List (A x)) x l y e)

postulate transport_List : (X : Set ℓ) (A : X → Set ℓ₁) (x : X) (l : List (A x)) (y : X) (e : Id X x y) →
                           transport (λ x → List (A x)) x l y e ≡ transport_List_ X A x l y e 

{-# REWRITE transport_List #-}

-- transporting over the identity is type casting

postulate cast_Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a) (e : _) →
                    transport (λ T → T) ((a : A) → B a) f ((a' : A') → B' a') e ≡
                    transport (λ X → (x : fst X) → (snd X) x) (A , B) f (A' , B') e

{-# REWRITE cast_Pi #-}

postulate cast_Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (s : Σ A B) (e : _) →
                    transport (λ T → T) (Σ A B) s (Σ A' B') e ≡
                    transport (λ X → Σ (fst X) (snd X)) (A , B) s (A' , B') e

{-# REWRITE cast_Sigma #-}

postulate cast_List : (A A' : Set ℓ) (l : List A) (e : _) →
                    transport (λ T → T) (List A) l (List A') e ≡
                    transport (λ T → List T) A l A' e

{-# REWRITE cast_List #-}


postulate transport_on_prop : (X : Set ℓ) (x : X) (P : Prop ℓ₁) (y : X) (e : Id X x y) →
                              transport (λ x → Prop ℓ₁) x P y e ≡ P
{-# REWRITE transport_on_prop #-}

-- sanity check on closed terms

test_J_refl_on_closed_term : (X : Set ℓ) (x : X) →
       transport (λ z → Σ ⊤ (λ z → ⊤)) x (tt , tt) x (Id_refl x) ≡ (tt , tt)
test_J_refl_on_closed_term X x = refl 

-- Quotient types

postulate Quotient : (A : Set ℓ)
                     (R : A → A → Prop ℓ)
                     (r : (x : A) → R x x)
                     (s : (x y : A) → R x y → R y x)
                     (t : (x y z : A) → R x y → R y z → R x z) →
                     Set ℓ

postulate pi : (A : Set ℓ)
               (R : A → A → Prop ℓ)
               (r : (x : A) → R x x)
               (s : (x y : A) → R x y → R y x)
               (t : (x y z : A) → R x y → R y z → R x z) →
               A → Quotient A R r s t

postulate Id_Quotient : (A : Set ℓ)
                        (R : A → A → Prop ℓ)
                        (r : (x : A) → R x x)
                        (s : (x y : A) → R x y → R y x)
                        (t : (x y z : A) → R x y → R y z → R x z)
                        (a a' : A) →
                        Id (Quotient A R r s t)
                           (pi A R r s t a) (pi A R r s t a') ≡ R a a'

{-# REWRITE Id_Quotient #-}

postulate Quotient_elim : (A : Set ℓ)
               (R : A → A → Prop ℓ)
               (r : (x : A) → R x x)
               (s : (x y : A) → R x y → R y x)
               (t : (x y z : A) → R x y → R y z → R x z)
               (P : Quotient A R r s t → Set ℓ₁) 
               (p : (x : A) → P (pi A R r s t x))
               (e : (x y : A) → (rel : R x y) →
                    Id _ (transport P (pi A R r s t x) (p x) (pi A R r s t y) rel) (p y))
               (w : Quotient A R r s t) → P w

postulate Quotient_elim_rec : (A : Set ℓ)
                (R : A → A → Prop ℓ)
                (r : (x : A) → R x x)
                (s : (x y : A) → R x y → R y x)
                (t : (x y z : A) → R x y → R y z → R x z)
                (P : Quotient A R r s t → Set ℓ₁) 
                (p : (x : A) → P (pi A R r s t x))
                (e : (x y : A) → (rel : R x y) →
                     Id _ (transport P (pi A R r s t x) (p x) (pi A R r s t y) rel) (p y))
                (a : A) →
                Quotient_elim A R r s t P p e (pi A R r s t a)
                ≡ p a

{-# REWRITE Quotient_elim_rec #-}

postulate transport_Quotient : (X : Set ℓ)
                  (A : X -> Set ℓ₁)
                  (R : (x : X) → A x → A x → Prop ℓ₁)
                  (r : (z : X) (x : A z) → R z x x)
                  (s : (z : X) (x y : A z) → R z x y → R z y x)
                  (t : (zz : X) (x y z : A zz) → R zz x y → R zz y z → R zz x z)
                  (x : X) (a : A x) (y : X) (e : Id X x y) →
                  transport (λ x → Quotient (A x) (R x) (r x) (s x) (t x))
                            x (pi (A x) (R x) (r x) (s x) (t x) a) y e
                  ≡ pi (A y) (R y) (r y) (s y) (t y) (transport A x a y e)

{-# REWRITE transport_Quotient #-}

postulate Id_Type_Quotient : (A A' : Set ℓ) 
                (R : A → A → Prop ℓ)
                (R' : A' → A' → Prop ℓ)
                (r : (x : A) → R x x)
                (r' : (x : A') → R' x x)
                (s : (x y : A) → R x y → R y x)
                (s' : (x y : A') → R' x y → R' y x)
                (t : (x y z : A) → R x y → R y z → R x z)
                (t' : (x y z : A') → R' x y → R' y z → R' x z) →
                Id (Set ℓ) (Quotient A R r s t) (Quotient A' R' r' s' t')
                ≡
                Id (Σ (Set ℓ) (λ A →
                    Σ (A → A → Prop ℓ) (λ R → Box (
                    Tel ((x : A) → R x x) (λ r →
                    Tel ((x y : A) → R x y → R y x) (λ s →
                      (x y z : A) → R x y → R y z → R x z))))))
                   (A , (R , box (r ,, (s ,, t))))
                   (A' , (R' , box (r' ,, (s' ,, t'))))

{-# REWRITE Id_Type_Quotient #-}
                  
postulate cast_Quotient : (A A' : Set ℓ) 
                (R : A → A → Prop ℓ)
                (R' : A' → A' → Prop ℓ)
                (r : (x : A) → R x x)
                (r' : (x : A') → R' x x)
                (s : (x y : A) → R x y → R y x)
                (s' : (x y : A') → R' x y → R' y x)
                (t : (x y z : A) → R x y → R y z → R x z)
                (t' : (x y z : A') → R' x y → R' y z → R' x z)
                (q : Quotient A R r s t) (e : _) →
                transport (λ T → T) (Quotient A R r s t) q
                                    (Quotient A' R' r' s' t') e ≡
                transport (λ (X : Σ (Set ℓ) (λ A →
                                  Σ (A → A → Prop ℓ) (λ R → Box (
                                  Tel ((x : A) → R x x) (λ r →
                                  Tel ((x y : A) → R x y → R y x) (λ s →
                                  (x y z : A) → R x y → R y z → R x z))))))
                                  → let struct = unbox (snd (snd X))
                                    in Quotient (fst X) (fst (snd X))
                                                (fstC struct)
                                                (fstC (sndC struct))
                                                (sndC (sndC struct)))
                          (A , (R , box (r ,, (s ,, t))))
                          q
                          (A' , (R' , box (r' ,, (s' ,, t'))))
                          e

{-# REWRITE cast_Quotient #-}

