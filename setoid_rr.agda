{-# OPTIONS --rewriting --prop --confluence-check #-}

open import Agda.Primitive
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.List
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit
open import Data.Vec.Base
open import Data.Bool

-- sigma type in Prop used to handle telescopes. 

record Tel {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,_
  field
    fstC : A
    sndC : B fstC

open Tel public

infixr 4 _,_

variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

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

{- 
 Axiomatisation of Id, Id-refl, transport and transport-refl (propositionally)

 Note that Id-refl, transport-Prop and transport-refl are axioms in Prop, 
 so we don't need to give them a computation content. 

 Also transport-refl is useless for transport on Prop
-}

postulate Id : (A : Set ℓ) → A → A → Prop ℓ

postulate Id-refl : {A : Set ℓ} (x : A) → Id A x x

postulate transport : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

postulate transport-prop : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

postulate transport-refl : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (e : Id A x x) → Id (P x) (transport P x t x e) t

-- direct derived functions 

inverse : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) → Id A y x
inverse A {x} {y} p = transport-prop (λ z → Id A z x) x (Id-refl x) y p

concatId : (A : Set ℓ) {x y z : A} (p : Id {ℓ} A x y)
         (q : Id {ℓ} A y z)→ Id A x z
concatId A {x} {y} {z} p q = transport-prop (λ t → Id A x t) y p z q

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A} (f : A → B) (e : Id A x y) →
     Id B (f x) (f y)
ap {ℓ} {ℓ₁} {A} {B} {x} {y} f e = transport-prop (λ z → Id B (f x) (f z)) x (Id-refl _) y e

-- we now state rewrite rules for the identity type

postulate Id-Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
                  Id ((a : A) → B a) f g ≡ ((a : A) → Id (B a) (f a) (g a))

{-# REWRITE Id-Pi #-}

-- rewrite rules on Id-refl are not needed because it is in Prop

refl-Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f : (a : A) → B a) →
          box (Id-refl f) ≡ box (λ a → Id-refl (f a))
refl-Pi A B f = refl

-- sanity check for funext

funext : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
         ((a : A) → Id (B a) (f a) (g a)) → Id ((a : A) → B a) f g  
funext A B f g e = e


postulate Id-Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (a a' : A)
                     (b : B a) (b' : B a') → 
                     Id (Σ A B) (a , b) (a' , b') ≡
                     Tel (Id A a a')
                         (λ e → Id (B a') (transport B a b a' e) b')

{-# REWRITE Id-Sigma #-}

postulate Id-Box : (A : Prop ℓ) (p q : A) → Id (Box A) (box p) (box q) ≡ ⊤P

{-# REWRITE Id-Box #-}

postulate Id-Unit : (p q : ⊤) → Id ⊤ p q ≡ ⊤P

{-# REWRITE Id-Unit #-}

postulate Id-list-nil-nil : (A : Set ℓ) →
                            Id (List A) [] [] ≡ ⊤P

-- postulate Id-list-nil-cons : (A : Set ℓ) (a' : A) (l' : List A) →
--                              Id (List A) [] (a' ∷ l') ≡ i ⊥

-- postulate Id-list-cons-nil : (A : Set ℓ) (a : A) (l : List A) →
--                              Id (List A) (a ∷ l) [] ≡ i ⊥

postulate Id-list-cons-cons : (A : Set ℓ) (a a' : A) (l l' : List A) →
                             Id (List A) (a ∷ l) (a' ∷ l') ≡
                             Id A a a' × Id (List A) l l'

{-# REWRITE Id-list-nil-nil #-}
{-# REWRITE Id-list-cons-cons #-}

postulate Id-nat-zero-zero : Id Nat 0 0 ≡ ⊤P

-- postulate Id-nat-zero-suc : (n : Nat) →
--                             Id Nat 0 (suc n) ≡ i ⊥

-- postulate Id-nat-suc-zero : (n : Nat) →
--                             Id Nat (suc n) zero ≡ i ⊥

postulate Id-nat-suc-suc : (n n' : Nat) →
                           Id Nat (suc n) (suc n') ≡
                           Id Nat n n'

{-# REWRITE Id-nat-zero-zero #-}
{-# REWRITE Id-nat-suc-suc #-}

postulate Id-bool-true-true : Id Bool true true ≡ ⊤P
postulate Id-bool-false-false : Id Bool false false ≡ ⊤P

{-# REWRITE Id-bool-true-true #-}
{-# REWRITE Id-bool-false-false #-}

-- rewrite rules for the identity type on the universe

telescope-Sigma : Set (lsuc (ℓ ⊔ ℓ₁))
telescope-Sigma {ℓ} {ℓ₁} = Σ (Set ℓ) (λ A → A → Set ℓ₁)

postulate Id-Type-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                          Id (Set (ℓ ⊔ ℓ₁)) (Σ A B) (Σ A' B') ≡
                          Id telescope-Sigma (A , B) (A' , B')

{-# REWRITE Id-Type-Sigma #-}

telescope-Forall : Set (lsuc (ℓ ⊔ ℓ₁))
telescope-Forall {ℓ} {ℓ₁} = Σ (Set ℓ) (λ A → A → Set ℓ₁)

postulate Id-Type-Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                       Id (Set (ℓ ⊔ ℓ₁)) ((a : A) → B a) ((a' : A') → B' a') ≡
                       Id telescope-Forall (A , B) (A' , B')

{-# REWRITE Id-Type-Pi #-}

telescope-List : Set (lsuc ℓ)
telescope-List {ℓ} = Set ℓ

postulate Id-Type-List : (A A' : Set ℓ) →
                       Id (Set ℓ) (List A) (List A') ≡
                       Id telescope-List A A'

{-# REWRITE Id-Type-List #-}

postulate Id-Type-Unit : Id Set ⊤ ⊤ ≡ ⊤P
                        
{-# REWRITE Id-Type-Unit #-}

postulate Id-Type-Nat : Id Set Nat Nat ≡ Id Set ⊤ ⊤
                        
{-# REWRITE Id-Type-Nat #-}

postulate Id-Type-Bool : Id Set Bool Bool ≡ Id Set ⊤ ⊤
                        
{-# REWRITE Id-Type-Bool #-}

telescope-Box : Set (lsuc ℓ)
telescope-Box {ℓ} = Prop ℓ

postulate Id-Type-Box : (P P' : Prop ℓ) → Id (Set ℓ) (Box P) (Box P') ≡ Id telescope-Box P P'
                        
{-# REWRITE Id-Type-Box #-}

-- rewrite rules for the identity type on Prop : Prop ext modulo cumul 

postulate Id-prop : (P Q : Prop ℓ) → Id (Prop ℓ) P Q ≡ i (P → Q) × (Q → P)

{-# REWRITE Id-prop #-}

-- Contractibility of singletons and J can be defined

contr-sing : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) →
    Id (Σ A (λ y → Box (Id A x y))) (x , box (Id-refl x)) (y , box p) 
contr-sing A {x} {y} p = p , ttP

J : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Set ℓ₁) 
    (t : P x (Id-refl x)) (y : A) (e : Id A x y) → P y e
J A x P t y e = transport (λ z → P (fst z) (unbox (snd z))) (x , box (Id-refl x)) t (y , box e) (contr-sing A e)

J-prop : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Prop ℓ₁) 
    (t : P x (Id-refl x)) (y : A) (e : Id A x y) → P y e
J-prop A x P t y e = transport-prop (λ z → P (fst z) (unbox (snd z))) (x , box (Id-refl x)) t (y , box e) (contr-sing A e)

-- tranporting back and forth is the identity

transport-inv : (X : Set ℓ) (A : X → Set ℓ₁) 
                (x : X) (y : X) (e : Id X x y) (a : A x) →
    Id (A x) (transport A y (transport A x a y e) x (inverse X e)) a
transport-inv X A x y e a = let e-refl = transport-refl A x a (Id-refl x)
                                e-refl-inv = inverse (A x) e-refl
                            in J-prop X x (λ y e → Id (A x) (transport A y (transport A x a y e) x (inverse X e)) a) (transport-prop (λ Z → Id (A x) (transport A x Z x (Id-refl x)) a) a e-refl _ e-refl-inv) y e

apD : {A : Set ℓ} {B : A → Set ℓ₁} {x y : A} (f : (a : A) → B a) (e : Id A x y) →
     Id (B y) (transport B x (f x) y e) (f y)
apD {ℓ} {ℓ₁} {A} {B} {x} {y} f e = J-prop _ x (λ z e → Id (B z) (transport B x (f x) z e) (f z)) (transport-refl B x (f x) (Id-refl x)) y e

-- we can now state rewrite rules for transports

postulate transport-Pi : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                         (x : X) (f : (a : A x) → B x a) (y : X) (e : Id X x y) →
                         transport (λ x → (a : A x) → B x a) x f y e ≡
                         λ (a' : A y) → let a = transport A y a' x (inverse X e)
                                        in transport (λ z → B (fst z) (snd z)) (x , a) (f a) (y , a')
                                                     (e , transport-inv X A y x (inverse X e) a') 

{-# REWRITE transport-Pi #-}

postulate transport-Sigma : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                            (x : X) (a : A x) (b : B x a) (y : X) (e : Id X x y) →
                            transport (λ z → Σ (A z) (B z)) x (a , b) y e ≡
                            (transport A x a y e , transport (λ z → B (fst z) (snd z)) _ b _ (e , Id-refl (transport A x a y e)))

{-# REWRITE transport-Sigma #-}

postulate transport-Unit : (X : Set ℓ) (x : X) (y : X) (e : Id X x y) →
                           transport (λ x → ⊤) x tt y e ≡ tt

{-# REWRITE transport-Unit #-}

postulate transport-Box : (X : Set ℓ) (A : X → Prop ℓ₁) (x : X) (a : A x) (y : X) (e : Id X x y) →
                           transport (λ x → Box (A x)) x (box a) y e ≡ box (transport-prop A x a y e)

{-# REWRITE transport-Box #-}

postulate transport-List-nil : (X : Set ℓ) (A : X → Set ℓ₁) (x : X) (y : X) (e : Id X x y) →
                               transport (λ x → List (A x)) x [] y e ≡ []

postulate transport-List-cons : (X : Set ℓ) (A : X → Set ℓ₁) (x : X) (a : A x) (l : List (A x))
                                (y : X) (e : Id X x y) →
                                transport (λ x → List (A x)) x (a ∷ l) y e ≡
                                transport A x a y e ∷ transport (λ x → List (A x)) x l y e

{-# REWRITE transport-List-nil #-}
{-# REWRITE transport-List-cons #-}

postulate transport-nat : (X : Set ℓ) (x : X) (y : X) (n : Nat) (e : Id X x y) →
                               transport (λ x → Nat) x n y e ≡ n

-- postulate transport-nat-suc : (X : Set ℓ) (x : X) (n : Nat)
--                               (y : X) (e : Id X x y) →
--                               transport (λ x → Nat) x (suc n) y e ≡
--                               suc (transport (λ x → Nat) x n y e)

{-# REWRITE transport-nat #-}
-- {-# REWRITE transport-nat-suc #-}

postulate transport-bool : (X : Set ℓ) (x : X) (y : X) (b : Bool) (e : Id X x y) →
                               transport (λ x → Bool) x b y e ≡ b

{-# REWRITE transport-bool #-}

postulate transport-on-prop : (X : Set ℓ) (x : X) (P : Prop ℓ₁) (y : X) (e : Id X x y) →
                              transport (λ x → Prop ℓ₁) x P y e ≡ P

{-# REWRITE transport-on-prop #-}

postulate transport-on-set : (X : Set ℓ) (x : X) (A : Set ℓ₁) (y : X) (e : Id X x y) →
                              transport (λ x → Set ℓ₁) x A y e ≡ A

{-# REWRITE transport-on-set #-}

-- transporting over the identity is type casting

postulate cast-Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a) (e : _) →
                    transport (λ T → T) ((a : A) → B a) f ((a' : A') → B' a') e ≡
                    transport (λ (X : telescope-Forall) → (x : fst X) → (snd X) x) (A , B) f (A' , B') e

{-# REWRITE cast-Pi #-}

postulate cast-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (s : Σ A B) (e : _) →
                    transport (λ T → T) (Σ A B) s (Σ A' B') e ≡
                    transport (λ (X : telescope-Sigma) → Σ (fst X) (snd X)) (A , B) s (A' , B') e

{-# REWRITE cast-Sigma #-}

postulate cast-List : (A A' : Set ℓ) (l : List A) (e : _) →
                    transport (λ T → T) (List A) l (List A') e ≡
                    transport (λ (T : telescope-List) → List T) A l A' e

{-# REWRITE cast-List #-}

postulate cast-Nat : (n : Nat) (e : _) →
                    transport (λ T → T) Nat n Nat e ≡
                    transport (λ T → Nat) ⊤ n ⊤ e

{-# REWRITE cast-Nat #-}

postulate cast-Bool : (b : Bool) (e : _) →
                    transport (λ T → T) Bool b Bool e ≡
                    transport (λ T → Bool) ⊤ b ⊤ e

{-# REWRITE cast-Bool #-}

postulate cast-Unit : (n : ⊤) (e : _) →
                    transport (λ T → T) ⊤ n ⊤ e ≡
                    transport (λ T → ⊤) ⊤ n ⊤ e

{-# REWRITE cast-Unit #-}

postulate cast-Box : (A A' : Prop ℓ) (l : Box A) (e : _) →
                    transport (λ T → T) (Box A) l (Box A') e ≡
                    transport (λ (T : telescope-Box) → Box T) A l A' e

{-# REWRITE cast-Box #-}

postulate weird-cast-app : (X : Set ℓ) (U : X → Set ℓ₁) (u : (x : X) → U x)  (t : (x : X) → (u : U x) → Set ℓ₂) (x y : X) (a : (t x) (u x)) (e : Id X x y) →
                      transport (λ x → (t x) (u x)) x a y e ≡
                      transport (λ (T : Set ℓ₂) → T) ((t x) (u x)) a ((t y) (u y)) (let e1 = apD t e (u y) in let e2 = ap (t x) (inverse (U x) (apD u (inverse X e))) in concatId (Set ℓ₂) { x = t x (u x) } { y = t x (transport U y (u y) x (inverse X e)) } { z = t y (u y) } e2 e1 ) 

-- not a valid rewrite rule
-- {-# REWRITE weird-cast-app #-}

weird-cast-fst : (B : Set → Set) (X Y : Σ Set B) (x : fst X) (e : _) →
                        transport (λ (T : Σ Set B) → fst T) X x Y e
                        ≡
                        transport (λ (T : Set) → T) (fst X) x (fst Y) (fstC e)
weird-cast-fst B X Y x e = weird-cast-app (Σ Set B) (λ X → ⊤) (λ X → tt) (λ X _ → fst X) X Y x e 


{-# REWRITE weird-cast-fst #-}

weird-cast-snd : (A : Set) (X Y : Σ A (λ _ → Set)) (x : snd X) (e : _) →
                        transport (λ (T : Σ A (λ _ → Set)) → snd T) X x Y e
                        ≡
                        transport (λ (T : Set) → T) (snd X) x (snd Y) (sndC e)
weird-cast-snd A X Y x e = weird-cast-app (Σ A (λ _ → Set)) (λ X → ⊤) (λ X → tt) (λ X _ → snd X) X Y x e 


{-# REWRITE weird-cast-snd #-}

weird-cast'' : (X Y : Σ Set (λ A → Σ A (λ _ → A → Set))) → (x : ((snd (snd X)) (fst (snd X)))) (e : _) →
                        transport (λ (T : Σ Set (λ A → Σ A (λ - → A → Set))) → ((snd (snd T)) (fst (snd T)))) X x Y e
                        ≡
                        transport (λ (T : Set) → T) (snd (snd X) (fst (snd X))) x (snd (snd Y) (fst (snd Y))) _

weird-cast'' X Y x e = weird-cast-app (Σ Set (λ A → Σ A (λ - → A → Set))) (λ X → fst X) (λ X → fst (snd X)) (λ X → snd (snd X)) X Y x e 

{-# REWRITE weird-cast'' #-}

-- sanity check on closed terms

foo : transport (λ (T : Σ Set (λ A → Σ A (λ _ → A → Set))) → ((snd (snd T)) (fst (snd T))))
                          (Nat , (0 , λ _ → Nat))
                          3
                          (Nat , (0 , λ _ → Nat))
                          (Id-refl {A = Σ Set (λ A → Σ A (λ _ → A → Set))} (Nat , (0 , λ _ → Nat)))
      ≡ 3
foo = refl

test-J-refl-on-closed-term : (X : Set ℓ) (x : X) →
       transport (λ z → Σ ⊤ (λ z → ⊤)) x (tt , tt) x (Id-refl x) ≡ (tt , tt)
test-J-refl-on-closed-term X x = refl 

-- Quotient types

{- 
  Note that r s and t are not used in the definitions, they are just here
  to make sure the theory stays consistent, because postulating the quotient, 
  we can derive them. In particular, with R = λ - - → ⊥, we would get
  a direct inconsistency using Id-refl
-}

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

telescope-Quotient : Set (lsuc ℓ)
telescope-Quotient {ℓ} = Σ (Set ℓ) (λ A →
                         Σ (A → A → Prop ℓ) (λ R → Box (
                         Tel ((x : A) → R x x) (λ r →
                         Tel ((x y : A) → R x y → R y x) (λ s →
                         (x y z : A) → R x y → R y z → R x z)))))

postulate Id-Quotient : (A : Set ℓ)
                        (R : A → A → Prop ℓ)
                        (r : (x : A) → R x x)
                        (s : (x y : A) → R x y → R y x)
                        (t : (x y z : A) → R x y → R y z → R x z)
                        (a a' : A) →
                        Id (Quotient A R r s t)
                           (pi A R r s t a) (pi A R r s t a') ≡ R a a'

{-# REWRITE Id-Quotient #-}

postulate Quotient-elim : (A : Set ℓ)
               (R : A → A → Prop ℓ)
               (r : (x : A) → R x x)
               (s : (x y : A) → R x y → R y x)
               (t : (x y z : A) → R x y → R y z → R x z)
               (P : Quotient A R r s t → Set ℓ₁) 
               (p : (x : A) → P (pi A R r s t x))
               (e : (x y : A) → (rel : R x y) →
                    Id _ (transport P (pi A R r s t x) (p x) (pi A R r s t y) rel) (p y))
               (w : Quotient A R r s t) → P w

postulate Quotient-elim-red : (A : Set ℓ)
                (R : A → A → Prop ℓ)
                (r : (x : A) → R x x)
                (s : (x y : A) → R x y → R y x)
                (t : (x y z : A) → R x y → R y z → R x z)
                (P : Quotient A R r s t → Set ℓ₁) 
                (p : (x : A) → P (pi A R r s t x))
                (e : (x y : A) → (rel : R x y) →
                     Id _ (transport P (pi A R r s t x) (p x) (pi A R r s t y) rel) (p y))
                (a : A) →
                Quotient-elim A R r s t P p e (pi A R r s t a)
                ≡ p a

{-# REWRITE Quotient-elim-red #-}

postulate Quotient-elim-prop : (A : Set ℓ)
               (R : A → A → Prop ℓ)
               (r : (x : A) → R x x)
               (s : (x y : A) → R x y → R y x)
               (t : (x y z : A) → R x y → R y z → R x z)
               (P : Quotient A R r s t → Prop ℓ₁) 
               (p : (x : A) → P (pi A R r s t x))
               (w : Quotient A R r s t) → P w

postulate transport-Quotient : (X : Set ℓ)
                  (A : X -> Set ℓ₁)
                  (R : (x : X) → A x → A x → Prop ℓ₁)
                  (r : (z : X) (x : A z) → R z x x)
                  (s : (z : X) (x y : A z) → R z x y → R z y x)
                  (t : (zz : X) (x y z : A zz) → R zz x y → R zz y z → R zz x z)
                  (x : X) (a : A x) (y : X) (e : Id X x y) →
                  transport (λ x → Quotient (A x) (R x) (r x) (s x) (t x))
                            x (pi (A x) (R x) (r x) (s x) (t x) a) y e
                  ≡ pi (A y) (R y) (r y) (s y) (t y) (transport A x a y e)

{-# REWRITE transport-Quotient #-}

postulate Id-Type-Quotient : (A A' : Set ℓ) 
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
                Id telescope-Quotient 
                   (A , (R , box (r , (s , t))))
                   (A' , (R' , box (r' , (s' , t'))))

{-# REWRITE Id-Type-Quotient #-}
                  
postulate cast-Quotient : (A A' : Set ℓ) 
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
                transport (λ (X : telescope-Quotient)
                                  → let struct = unbox (snd (snd X))
                                    in Quotient (fst X) (fst (snd X))
                                                (fstC struct)
                                                (fstC (sndC struct))
                                                (sndC (sndC struct)))
                          (A , (R , box (r , (s , t))))
                          q
                          (A' , (R' , box (r' , (s' , t'))))
                          e

{-# REWRITE cast-Quotient #-}

-- Sanity Check: transport-refl oon quotient type

transport-refl-Quotient : (X : Set ℓ)
                  (A : X -> Set ℓ₁)
                  (R : (x : X) → A x → A x → Prop ℓ₁)
                  (r : (z : X) (x : A z) → R z x x)
                  (s : (z : X) (x y : A z) → R z x y → R z y x)
                  (t : (zz : X) (x y z : A zz) → R zz x y → R zz y z → R zz x z)
                  (x : X) (q : Quotient (A x) (R x) (r x) (s x) (t x))
                  (e : Id X x x) →
                  Id _
                    (transport (λ x → Quotient (A x) (R x) (r x) (s x) (t x))
                               x q x e)
                    q
transport-refl-Quotient X A R r s t x q e =
  Quotient-elim-prop (A x) (R x) (r x) (s x) (t x)
                     ((λ a → Id _ (transport (λ (x : X) → Quotient (A x) (R x) (r x) (s x) (t x)) x a x e) a))
                     (λ a → transport-prop (λ a' → R x a' a) a (r x a) (transport A x a x e) ((inverse (A x) (transport-refl A x a e)))) q

-- Vector (or how to deal with indices)
-- Some of the rewrite rules below can be defined only because
-- the indexes of vnil and vcons are given by constructor of Nat

telescope-Vec : Set (lsuc ℓ)
telescope-Vec {ℓ} = Σ (Set ℓ) (λ - → Nat)

postulate Id-vector-vnil-vnil : (A : Set ℓ) →
                            Id (Vec A 0) [] [] ≡ ⊤P

-- postulate Id-vector-vnil-vcons : not well typed
-- postulate Id-vector-vcons-vnil : not well typed

postulate Id-vector-vcons-vcons : (A : Set ℓ) (n : Nat) (a a' : A)
                                  (l l' : Vec A n) →
                                  Id (Vec A (suc n)) (a ∷ l) (a' ∷ l') ≡
                                  Id A a a' × Id (Vec A n) l l'

{-# REWRITE Id-vector-vnil-vnil #-}
{-# REWRITE Id-vector-vcons-vcons #-}

postulate Id-Type-Vec : (A A' : Set ℓ) (n n' : Nat) →
                       Id (Set ℓ) (Vec A n) (Vec A' n') ≡
                       Id telescope-Vec (A , n) (A' , n') 

{-# REWRITE Id-Type-Vec #-}

postulate transport-Vec-vnil : (X : Set ℓ) (A : X → Set ℓ₁)
                                  (x : X) (y : X) (e : Id X x y) →
                       transport (λ x → Vec (A x) 0) x [] y e ≡ []

postulate transport-Vec-vcons : (X : Set ℓ) (A : X → Set ℓ₁) (n : X → Nat)
                                   (x : X) (a : A x) (l : Vec (A x) (n x))
                                   (y : X) (e : Id X x y) →
                       transport (λ (z : X) → Vec (A z) (suc (n z))) x (_∷_ {A = {- ! -} A x} {n = {- ! -} n x} a l) y e ≡
                       transport A x a y e ∷ transport (λ z → Vec (A z) (n z)) x l y e

{- Note that the rule above is technically non-linear, but the arguments A and n of vcons can be seen as "type-forced" -}

{-# REWRITE transport-Vec-vnil #-}
{-# REWRITE transport-Vec-vcons #-}

postulate cast-Vec : (A A' : Set ℓ) (n n' : Nat) (v : Vec A n) (e : _) →
                    transport (λ T → T) (Vec A n) v (Vec A' n') e ≡
                    transport (λ (X : telescope-Vec) → Vec (fst X) (snd X)) (A , n) v (A' , n') e

{-# REWRITE cast-Vec #-}

-- Test with weird vectors indexed by lists.

data VecL (A : Set ℓ) (a : A) : List A → Set ℓ where
  []  : VecL A a []
  _∷_ : {l : List A} → A → VecL A a l → VecL A a (a ∷ l)

telescope-VecL : Set (lsuc ℓ)
telescope-VecL {ℓ} = Σ (Set ℓ) (λ A → Σ A (λ - → List A))

postulate Id-vectorL-vnil-vnil : (A : Set ℓ) (a : A) →
                            Id (VecL A a []) [] [] ≡ ⊤P

-- postulate Id-vector-vnil-vcons : not well typed
-- postulate Id-vector-vcons-vnil : not well typed

postulate Id-vectorL-vcons-vcons : (A : Set ℓ) (x : A) (l : List A) (a a' : A)
                                  (v v' : VecL A x l) →
                                  Id (VecL A x (x ∷ l)) (a ∷ v) (a' ∷ v') ≡
                                  Id A a a' × Id (VecL A x l) v v'

{-# REWRITE Id-vectorL-vnil-vnil #-}
{-# REWRITE Id-vectorL-vcons-vcons #-}

postulate Id-Type-VecL : (A A' : Set ℓ) (a : A) (a' : A') (l : List A) (l' : List A') →
                       Id (Set ℓ) (VecL A a l) (VecL A' a' l') ≡
                       Id telescope-VecL (A , (a , l)) (A' , (a' , l'))

{-# REWRITE Id-Type-VecL #-}

postulate transport-VecL-vnil : (X : Set ℓ) (A : X → Set ℓ₁) (Val : (x : X) → A x)
                                (x : X) (y : X) (e : Id X x y) →
                       transport (λ x → VecL (A x) (Val x) []) x [] y e ≡ []

postulate transport-VecL-vcons : (X : Set ℓ) (A : X → Set ℓ₁) (Val : (x : X) → A x) (l : (x : X) → List (A x))
                                   (x : X) (a : A x) (v : VecL (A x) (Val x) (l x))
                                   (y : X) (e : Id X x y) →
                       transport (λ (z : X) → VecL (A z) (Val z) (Val z ∷ l z)) x (a ∷ v) y e ≡
                       transport A x a y e ∷ transport (λ z → VecL (A z) (Val z) (l z)) x v y e

{-# REWRITE transport-VecL-vnil #-}
{-# REWRITE transport-VecL-vcons #-}

postulate cast-VecL : (A A' : Set ℓ) (a : A) (a' : A') (l : List A) (l' : List A') (v : VecL A a l) (e : _) →
                    transport (λ T → T) (VecL A a l) v ( VecL A' a' l') e ≡
                    transport (λ (X : telescope-VecL) → VecL (fst X) (fst (snd X)) (snd (snd X))) (A , (a , l)) v (A' , (a' , l')) e

{-# REWRITE cast-VecL #-}

-- Now for Path

telescope-Path : Set (lsuc ℓ)
telescope-Path {ℓ} = Σ (Set ℓ) (λ A → Σ A (λ - → A))

postulate Id-Path : (A : Set ℓ) (x : A) →
                    Id (x ≡ {- ! -} x) (refl) (refl) ≡ ⊤P


{-# REWRITE Id-Path #-}

postulate Id-Type-Path : (A A' : Set ℓ) (x y : A) (x' y' : A') →
                       Id (Set ℓ) (x ≡ y) (x' ≡ y') ≡
                       Id telescope-Path (A , (x , y)) (A' , (x' , y'))

{-# REWRITE Id-Type-Path #-}


postulate transport-Path : (X : Set ℓ) (A : X → Set ℓ₁)
                           (a : (x : X) → A x)
                           (x : X) (y : X) (e : Id X x y) →
                           transport (λ x → a x ≡ {- ! -} a x) x (refl) y e ≡
                           refl

-- This rewrite rule is not valid as it is non-linear or we need to accept rewrite rules with "type-forced" arguments such as
-- transport (λ x → a x ≡ !{a x}) x (refl {x = !{a x}}) y e ≡ refl {x = a y}

{-# REWRITE transport-Path #-}


-- postulate transport-Path' : (X : Set ℓ) (A : Set ℓ₁)
--                             (a : (x : X) → A)
--                             (x : X) (y : X) (e : Id X x y) →
--                             transport (λ y → a x ≡ a y) x (refl) y e ≡
--                             ?

-- {-# REWRITE transport-Path' #-}

postulate cast-Path : (A A' : Set ℓ) (x y : A) (x' y' : A') (p : x ≡ y) (e : _) →
                    transport (λ T → T) (x ≡ y) p (x' ≡ y') e ≡
                    transport (λ (X : telescope-Path) → fst (snd X) ≡ snd (snd X))
                              (A , (x , y)) p (A' , (x' , y')) e  

{-# REWRITE cast-Path #-}

id-to-Path : {A : Set ℓ} {x y : A} → Id A x y → x ≡ y
id-to-Path {ℓ} {A} {x} {y} = transport (λ (z : A) → x ≡ z) x (refl) y 

path-to-Id : {A : Set ℓ} {x y : A} → x ≡ y → Id A x y 
path-to-Id {ℓ} {A} {x} {y} refl = Id-refl x

funext' : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
          ((a : A) → f a ≡ g a) → f ≡ g 
funext' A B f g e = id-to-Path (λ (a : A) → path-to-Id (e a))

etaBool : (a : Bool) → a ≡ (if a then true else false)
etaBool true = refl
etaBool false = refl

etaBool- : (a : Bool) → Id Bool a (if a then true else false)
etaBool- true = Id-refl true
etaBool- false = Id-refl false

test- : Id _  (λ (b : Bool) → b) (λ (b : Bool) → if b then true else false)
test- = λ a → etaBool- a

test : (λ (b : Bool) → b) ≡ (λ (b : Bool) → if b then true else false)
test = funext' Bool (λ - → Bool) _ _ λ a → etaBool a

transportEq : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : x ≡ y) → P y
transportEq P x t y refl = t

test'- : Bool
test'- = transport (λ f → Bool) (λ (b : Bool) → b) true (λ (b : Bool) → if b then true else false) test- 

test' : Bool
test' = transportEq (λ f → Bool) (λ (b : Bool) → b) true (λ (b : Bool) → if b then true else false) test 

