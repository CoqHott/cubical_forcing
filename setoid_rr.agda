{-# OPTIONS --rewriting --prop --cumulativity #-}

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
open import Data.Sum

-- sigma type in Prop used to handle telescopes. 

record Tel {a b} (A : Prop a) (B : A → Prop b) : Prop (a ⊔ b) where
  constructor _,_
  field
    fstC : A
    sndC : B fstC

open Tel public

infixr 4 _,_

record ΣCov {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    fstCov : A
    sndCov : B fstCov

open ΣCov public

variable ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

-- a bit of boilerplate to deal with Prop

data ⊥ : Prop where

⊥-elim : {A : Set ℓ} → ⊥ → A
⊥-elim () 

record ⊤P : Prop ℓ where
  constructor ttP

record Box (A : Prop ℓ) : Set ℓ where
  constructor box
  field
    unbox : A

open Box public

_×_ : ∀ (A : Prop ℓ) (B : Prop ℓ₁) → Prop (ℓ ⊔ ℓ₁)
A × B = Tel A (λ _ → B)

{- 
 Axiomatisation of Id, Id-refl, transport (for proposition), cast 

 Note that Id-refl, transport are axioms in Prop, 
 so we don't need to give them a computation content. 

 Also transport-refl is useless for transport on Prop
-}

postulate Id : (A : Set ℓ) → A → A → Prop ℓ

postulate cast : (A B : Set ℓ) (e : Id {lsuc ℓ} (Set ℓ) A B) → A → B 

postulate Id-refl : {A : Set ℓ} (x : A) → Id A x x

postulate cast-refl : {A : Set ℓ} (e : Id {lsuc ℓ} (Set ℓ) A A) (a : A) → Id A (cast {ℓ = ℓ} A A e a) a

postulate transport : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

-- direct derived functions 

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A} (f : A → B) (e : Id A x y) →
     Id B (f x) (f y)
ap {ℓ} {ℓ₁} {A} {B} {x} {y} f e = transport (λ z → Id B (f x) (f z)) x (Id-refl _) y e

transport-Id : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y
transport-Id {ℓ} {ℓ₁} P x t y e = cast {ℓ = ℓ₁} (P x) (P y) (ap P e) t

transport-refl : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (e : Id {ℓ} A x x) → Id _ (transport-Id P x t x e) t
transport-refl {ℓ} {ℓ₁} P x t e = cast-refl (ap P e) t

inverse  : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) → Id A y x
inverse {ℓ} A {x} {y} p = transport {ℓ = ℓ} {ℓ₁ = ℓ} (λ z → Id {ℓ = ℓ} A z x) x (Id-refl x) y p

-- concatId : (A : Set ℓ) {x y z : A} (p : Id {ℓ} A x y)
--            (q : Id {ℓ} A y z) → Id A x z
-- concatId A {x} {y} {z} p q = transport (λ t → Id A x t) y p z q

-- we now state rewrite rules for the identity type

postulate Id-Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
                  Id {ℓ ⊔ ℓ₁} ((a : A) → B a) f g ≡ ((a : A) → Id {ℓ₁} (B a) (f a) (g a))


{-# REWRITE Id-Pi #-}

-- rewrite rules on Id-refl are not needed because it is in Prop

refl-Pi : (A : Set ℓ) (B : A → Set ℓ₁) (f : (a : A) → B a) →
          box (Id-refl {ℓ ⊔ ℓ₁} f) ≡ box (λ a → Id-refl {ℓ₁} (f a))
refl-Pi A B f = refl

-- sanity check for funext

funext : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
         ((a : A) → Id (B a) (f a) (g a)) → Id ((a : A) → B a) f g  
funext A B f g e = e

postulate Id-Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (a a' : A)
                     (b : B a) (b' : B a') → 
                     Id {ℓ ⊔ ℓ₁} (Σ A B) (a , b) (a' , b') ≡
                     Tel (Id {ℓ} A a a')
                         (λ e → Id (B a') (transport-Id B a b a' e) b')

{-# REWRITE Id-Sigma #-}

postulate Id-SigmaCov : (A : Set ℓ) (B : A → Set ℓ₁) (a a' : A)
                     (b : B a) (b' : B a') → 
                     Id {ℓ ⊔ ℓ₁} (ΣCov A B) (a , b) (a' , b') ≡
                     Tel (Id {ℓ} A a a')
                         (λ e → Id (B a) b (transport-Id B a' b' a (inverse {ℓ} A e)))

{-# REWRITE Id-SigmaCov #-}

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

postulate Id-list-cons-cons : (A : Set ℓ) (a a' : A) (l l' : List {ℓ} A) →
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


postulate Id-sum-inj₁-inj₁ : (A : Set ℓ) (B : Set ℓ₁) (a a' : A) →
                           Id (A ⊎ B) (inj₁ a) (inj₁ a') ≡
                           Id A a a'

postulate Id-sum-inj₂-inj₂ : (A : Set ℓ) (B : Set ℓ₁) (b b' : B) →
                           Id (A ⊎ B) (inj₂ b) (inj₂ b') ≡
                           Id B b b'

{-# REWRITE Id-sum-inj₁-inj₁ #-}
{-# REWRITE Id-sum-inj₂-inj₂ #-}

-- rewrite rules for the identity type on the universe

telescope-Sigma : Set (lsuc (ℓ ⊔ ℓ₁))
telescope-Sigma {ℓ} {ℓ₁} = ΣCov (Set ℓ) (λ A → A → Set ℓ₁)

postulate Id-Type-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                          Id {lsuc (ℓ ⊔ ℓ₁)} (Set (ℓ ⊔ ℓ₁)) (Σ A B) (Σ A' B') ≡
                          Id {lsuc (ℓ ⊔ ℓ₁)} telescope-Sigma (A , B) (A' , B')

{-# REWRITE Id-Type-Sigma #-}

telescope-Forall : Set (lsuc (ℓ ⊔ ℓ₁))
telescope-Forall {ℓ} {ℓ₁} = Σ (Set ℓ) (λ A → A → Set ℓ₁)

postulate Id-Type-Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) →
                       Id {lsuc (ℓ ⊔ ℓ₁)} (Set (ℓ ⊔ ℓ₁)) ((a : A) → B a) ((a' : A') → B' a') ≡
                       Id {lsuc (ℓ ⊔ ℓ₁)} telescope-Forall (A , B) (A' , B')

{-# REWRITE Id-Type-Pi #-}

telescope-Sum : Set (lsuc (ℓ ⊔ ℓ₁))
telescope-Sum {ℓ} {ℓ₁} = Σ (Set ℓ) (λ _ → Set ℓ₁)

postulate Id-Type-Sum : (A A' : Set ℓ) (B B' : Set ℓ₁)  →
                          Id {lsuc (ℓ ⊔ ℓ₁)} (Set (ℓ ⊔ ℓ₁)) (A ⊎ B) (A' ⊎ B') ≡
                          Id {lsuc (ℓ ⊔ ℓ₁)} telescope-Sum (A , B) (A' , B')

{-# REWRITE Id-Type-Sum #-}

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

postulate Id-prop : (P Q : Prop ℓ) → Id (Prop ℓ) P Q ≡ (P → Q) × (Q → P)

{-# REWRITE Id-prop #-}


postulate Id-set : Id (Set (lsuc ℓ₁)) (Set ℓ₁) (Set ℓ₁) ≡ ⊤P

{-# REWRITE Id-set #-}

-- non-diagonal cases

{- There are n^2 cases, that's a pain, this is not exhaustive for the moment -}

postulate Id-set-nat : Id _ (Set ℓ) Nat ≡ ⊥
postulate Id-nat-set : Id (Set (lsuc ℓ)) Nat (Set ℓ) ≡ ⊥
postulate Id-set-bool : Id _ (Set ℓ) Bool ≡ ⊥
postulate Id-bool-set : Id (Set (lsuc ℓ)) Bool (Set ℓ) ≡ ⊥
postulate Id-bool-nat : Id (Set ℓ) Bool Nat ≡ ⊥
postulate Id-nat-bool : Id (Set ℓ) Nat Bool ≡ ⊥
postulate Id-set-pi : (A : Set ℓ₁) (B : A → Set ℓ₂) → Id (Set (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)) (Set ℓ) ((a : A) → B a)  ≡ ⊥
postulate Id-pi-set : (A : Set ℓ₁) (B : A → Set ℓ₂) → Id (Set (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)) ((a : A) → B a) (Set ℓ)  ≡ ⊥
postulate Id-set-sigma : (A : Set ℓ₁) (B : A → Set ℓ₂) → Id (Set (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)) (Set ℓ) (Σ A B) ≡ ⊥
postulate Id-sigma-set : (A : Set ℓ₁) (B : A → Set ℓ₂) → Id (Set (lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂)) (Σ A B) (Set ℓ) ≡ ⊥

{-# REWRITE Id-set-nat Id-nat-set Id-set-bool Id-bool-set Id-bool-nat Id-nat-bool Id-set-pi Id-pi-set Id-set-sigma Id-sigma-set #-}

--- Contractibility of singletons and J can be defined

contr-sing : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) →
    Id {ℓ} (Σ A (λ y → Box (Id {ℓ} A x y))) (x , box (Id-refl {ℓ} x)) (y , box p) 
contr-sing A {x} {y} p = p , ttP

J : (A : Set ℓ) (x : A) (P : (y : A) → Id {ℓ} A x y → Prop ℓ₁) 
    (t : P x (Id-refl {ℓ} x)) (y : A) (e : Id {ℓ} A x y) → P y e
J {ℓ} {ℓ₁} A x P t y e = transport {ℓ = ℓ} {ℓ₁ = ℓ₁} (λ (z : Σ {ℓ} {ℓ} A (λ y → Box {ℓ = ℓ} (Id {ℓ} A x y))) → P (fst z) (unbox {ℓ = ℓ} (snd z)))
                                   (x , box (Id-refl {ℓ = ℓ} x)) t (y , box e) (contr-sing {ℓ = ℓ} A e)

-- tranporting back and forth is the identity

-- cast-inv : (A B : Set ℓ) (e : Id _ A B) (a : A) →
--                      Id A (cast B A (inverse (Set ℓ) {x = A} {y = B} e) (cast A B e a)) a
-- cast-inv {ℓ} A B e a = let e-refl = cast-refl (Id-refl A) a in
--                        let e-refl-cast = cast-refl (Id-refl A) (cast A A (Id-refl A) a) in
--                        J (Set ℓ) A (λ B e → Id A (cast B A (inverse (Set ℓ) {x = A} {y = B} e) (cast A B e a)) a)
--                          (concatId A e-refl-cast e-refl) B e


postulate cast-set : (A : Set ℓ) (e : _) → cast {lsuc ℓ} (Set ℓ) (Set ℓ) e A ≡ A

{-# REWRITE cast-set #-}

postulate cast-prop : (A : Prop ℓ) (e : _) → cast (Prop ℓ) (Prop ℓ) e A ≡ A

{-# REWRITE cast-prop #-}

postulate cast-type-family : (A A' : Set ℓ) (f : (a : A) → Set ℓ₁) (e : Id {lsuc (ℓ ⊔ lsuc ℓ₁)} (Set (ℓ ⊔ lsuc ℓ₁)) ((a : A) → Set ℓ₁) ((a' : A') → Set ℓ₁)) →
                    cast {ℓ ⊔ lsuc ℓ₁} ((a : A) → Set ℓ₁) ((a' : A') → Set ℓ₁) e f ≡
                    λ (a' : A') → let a = cast {ℓ} A' A (inverse {lsuc ℓ} (Set ℓ) {x = A} {y = A'} (fstC e)) a' in f a 

{-# REWRITE cast-type-family #-}

postulate cast-Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a)
                    (e : Id {lsuc (ℓ ⊔ ℓ₁)} (Set (ℓ ⊔ ℓ₁)) ((a : A) → B a) ((a' : A') → B' a')) →
                    cast {ℓ ⊔ ℓ₁} ((a : A) → B a) ((a' : A') → B' a') e f ≡
                    let eAA' = fstC e
                    in λ (a' : A') → let a = cast {ℓ} A' A (inverse {lsuc ℓ} (Set ℓ) {x = A} {y = A'} eAA') a' in
                                     cast {ℓ₁} (B (cast {ℓ} A' A (inverse {lsuc ℓ} (Set ℓ) {x = A} {y = A'} eAA') a')) (B' a') (sndC e a') (f a)

{-# REWRITE cast-Pi #-}


postulate cast-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (x : A) (y : B x)
                       (e : Id {lsuc (ℓ ⊔ ℓ₁)} (Set (ℓ ⊔ ℓ₁)) (Σ {ℓ} {ℓ₁} A B) (Σ {ℓ} {ℓ₁} A' B')) →
                       let eA = fstC e in
                       let x' = cast {ℓ} A A' eA x in 
                       let eB = sndC e x in
                       cast {ℓ ⊔ ℓ₁} (Σ {ℓ} {ℓ₁} A B) (Σ {ℓ} {ℓ₁} A' B') e (x , y) ≡
                         (cast {ℓ} A A' eA x , cast {ℓ₁} (B x) (B' x') eB y)

{-# REWRITE cast-Sigma #-}
 
postulate cast-Sum-inj₁ : (A A' : Set ℓ) (B B' : Set ℓ₁) (a : A) (e : Id {lsuc (ℓ ⊔ ℓ₁)} (Set (ℓ ⊔ ℓ₁)) (_⊎_ {ℓ} {ℓ₁} A B) (_⊎_ {ℓ} {ℓ₁} A' B')) →
                    let eA = fstC e in
                    let eB = sndC e in
                    cast {ℓ ⊔ ℓ₁} (_⊎_ {ℓ} {ℓ₁} A B) (_⊎_ {ℓ} {ℓ₁} A' B') e (inj₁ a) ≡
                    inj₁ (cast {ℓ} A A' eA a)

postulate cast-Sum-inj₂ : (A A' : Set ℓ) (B B' : Set ℓ₁) (b : B) (e : Id {lsuc (ℓ ⊔ ℓ₁)} (Set (ℓ ⊔ ℓ₁)) (_⊎_ {ℓ} {ℓ₁} A B) (_⊎_ {ℓ} {ℓ₁} A' B')) →
                    let eA = fstC e in
                    let eB = sndC e in
                    cast {ℓ ⊔ ℓ₁} (_⊎_ {ℓ} {ℓ₁} A B) (_⊎_ {ℓ} {ℓ₁} A' B') e (inj₂ b) ≡
                    inj₂ (cast {ℓ₁} B B' eB b)


{-# REWRITE cast-Sum-inj₁ #-}
{-# REWRITE cast-Sum-inj₂ #-}

postulate cast-List-nil : (A A' : Set ℓ) (e : _) →
                          cast {ℓ} (List {ℓ} A) (List {ℓ} A') e [] ≡ []

postulate cast-List-cons : (A A' : Set ℓ) (e : _) (a : A) (l : List {ℓ} A) →
                           cast {ℓ} (List {ℓ} A) (List {ℓ} A') e (a ∷ l) ≡
                           cast {ℓ} A A' e a ∷ cast {ℓ} _ _ e l

{-# REWRITE cast-List-nil #-}

{-# REWRITE cast-List-cons #-}

postulate cast-Nat-zero : (e : _) → cast Nat Nat e 0 ≡ 0

postulate cast-Nat-suc : (e : _) (n : Nat ) →
                          cast {lzero} Nat Nat e (suc n) ≡
                          suc (cast {lzero} _ _ e n)

{-# REWRITE cast-Nat-zero #-}

{-# REWRITE cast-Nat-suc #-}

postulate cast-Bool-true : (e : _) → cast Bool Bool e true ≡ true

{-# REWRITE cast-Bool-true #-}

postulate cast-Bool-false : (e : _) → cast Bool Bool e false ≡ false

{-# REWRITE cast-Bool-false #-}

postulate cast-Unit : (e : _) → cast ⊤ ⊤ e tt ≡ tt

{-# REWRITE cast-Unit #-}


postulate cast-Box : (A A' : Prop ℓ) (a : A) (f : _) (g : _) →
                    cast {ℓ} (Box {ℓ} A) (Box {ℓ} A') (f , g) (box a) ≡ box (f a)

{-# REWRITE cast-Box #-}

-- impossible casts

postulate cast-set-nat :  (e : _) (x : _) → cast {lsuc ℓ} (Set ℓ) Nat e x ≡ ⊥-elim e
postulate cast-nat-set :  (e : _) (x : _) → cast {lsuc ℓ} Nat (Set ℓ) e x ≡ ⊥-elim e
postulate cast-set-bool : (e : _) (x : _) → cast {lsuc ℓ} (Set ℓ) Bool e x ≡ ⊥-elim e 
postulate cast-bool-set : (e : _) (x : _) → cast {lsuc ℓ} Bool (Set ℓ) e x ≡ ⊥-elim e
postulate cast-bool-nat : (e : _) (x : _) → cast {ℓ} Bool Nat e x ≡ ⊥-elim e
postulate cast-nat-bool : (e : _) (x : _) → cast {ℓ} Nat Bool e x ≡ ⊥-elim e
postulate cast-set-pi : (A : Set ℓ₁) (B : A → Set ℓ₂) (e : _) (x : _) → cast {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Set ℓ) ((a : A) → B a) e x ≡ ⊥-elim e
postulate cast-pi-set : (A : Set ℓ₁) (B : A → Set ℓ₂) (e : _) (x : _) → cast {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} ((a : A) → B a) (Set ℓ) e x ≡ ⊥-elim e
postulate cast-set-sigma : (A : Set ℓ₁) (B : A → Set ℓ₂) (e : _) (x : _) → cast {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Set ℓ) (Σ {ℓ₁} {ℓ₂} A B) e x ≡ ⊥-elim e 
postulate cast-sigma-set : (A : Set ℓ₁) (B : A → Set ℓ₂) (e : _) (x : _) → cast {lsuc ℓ ⊔ ℓ₁ ⊔ ℓ₂} (Σ {ℓ₁} {ℓ₂} A B) (Set ℓ) e x ≡ ⊥-elim e

{-# REWRITE cast-set-nat cast-nat-set cast-set-bool cast-bool-set cast-bool-nat cast-nat-bool cast-set-pi cast-pi-set  cast-set-sigma cast-sigma-set #-}

-- sanity check on closed terms
{-
foo : transport-Id (λ (T : Σ {lsuc lzero} {lsuc lzero} Set (λ A → Σ {lzero} {lsuc lzero} A (λ _ → A → Set))) → ((snd (snd T)) (fst (snd T))))
                          (Nat , (0 , λ _ → Nat))
                          3
                          (Nat , (0 , λ _ → Nat))
                          (Id-refl {lsuc lzero} {A = Σ {lsuc lzero} {lsuc lzero} Set (λ A → Σ {lzero} {lsuc lzero} A (λ _ → A → Set))} (Nat , (0 , λ _ → Nat)))
      ≡ 3
foo = refl
-}

test-J-refl-on-closed-term : (X : Set ℓ) (x : X) →
       transport-Id {ℓ} (λ z → Σ {lzero} {lzero} ⊤ (λ z → ⊤)) x (tt , tt) x (Id-refl {ℓ} x) ≡ (tt , tt)
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
                        Id {ℓ} (Quotient {ℓ} A R r s t)
                           (pi A R r s t a) (pi A R r s t a') ≡ R a a'

{-# REWRITE Id-Quotient #-}

postulate Quotient-elim : (A : Set ℓ)
               (R : A → A → Prop ℓ)
               (r : (x : A) → R x x)
               (s : (x y : A) → R x y → R y x)
               (t : (x y z : A) → R x y → R y z → R x z)
               (P : Quotient {ℓ} A R r s t → Set ℓ₁) 
               (p : (x : A) → P (pi {ℓ} A R r s t x))
               (e : (x y : A) → (rel : R x y) →
                    Id {ℓ₁} _ (transport-Id {ℓ} P (pi {ℓ} A R r s t x) (p x) (pi {ℓ} A R r s t y) rel) (p y))
               (w : Quotient {ℓ} A R r s t) → P w

postulate Quotient-elim-red : (A : Set ℓ)
               (R : A → A → Prop ℓ)
               (r : (x : A) → R x x)
               (s : (x y : A) → R x y → R y x)
               (t : (x y z : A) → R x y → R y z → R x z)
               (P : Quotient {ℓ} A R r s t → Set ℓ₁) 
               (p : (x : A) → P (pi {ℓ} A R r s t x))
               (e : _)
               (a : A) →
               Quotient-elim {ℓ} {ℓ₁} A R r s t P p e (pi {ℓ} A R r s t a)
               ≡ p a

{-# REWRITE Quotient-elim-red #-}

postulate Quotient-elim-prop : (A : Set ℓ)
               (R : A → A → Prop ℓ)
               (r : (x : A) → R x x)
               (s : (x y : A) → R x y → R y x)
               (t : (x y z : A) → R x y → R y z → R x z)
               (P : Quotient {ℓ} A R r s t → Prop ℓ₁) 
               (p : (x : A) → P (pi {ℓ} A R r s t x))
               (w : Quotient {ℓ} A R r s t) → P w

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
                (a : A) (e : _) →
                cast {ℓ} (Quotient {ℓ} A R r s t) (Quotient {ℓ} A' R' r' s' t') e (pi A R r s t a) ≡
                pi {ℓ} A' R' r' s' t' (cast {ℓ} A A' (fstC e) a)

{-# REWRITE cast-Quotient #-}


-- Sanity Check: transport-refl on quotient type
{-
transport-refl-Quotient : (X : Set ℓ)
                  (A : X -> Set ℓ₁)
                  (R : (x : X) → A x → A x → Prop ℓ₁)
                  (r : (z : X) (x : A z) → R z x x)
                  (s : (z : X) (x y : A z) → R z x y → R z y x)
                  (t : (zz : X) (x y z : A zz) → R zz x y → R zz y z → R zz x z)
                  (x : X) (q : Quotient {ℓ₁} (A x) (R x) (r x) (s x) (t x))
                  (e : Id {ℓ} X x x) →
                  Id {ℓ₁} _
                    (transport-Id {ℓ} (λ x → Quotient {ℓ₁} (A x) (R x) (r x) (s x) (t x))
                               x q x e)
                    q
transport-refl-Quotient {ℓ} {ℓ₁} X A R r s t x q e =
  Quotient-elim-prop {ℓ = ℓ₁} (A x) (R x) (r x) (s x) (t x)
                     ((λ a → Id _ (transport-Id (λ (x : X) → Quotient (A x) (R x) (r x) (s x) (t x)) x a x e) a))
                     (λ a →  transport (λ a' → R x a' a) a (r x a) (cast (A x) (A x) _ a) (inverse (A x) (transport-refl A x a e)))
                     q
-}

-- Vector (or how to deal with indices)
-- Some of the rewrite rules below can be defined only because
-- the indexes of vnil and vcons are given by constructor of Nat

telescope-Vec : Set (lsuc ℓ)
telescope-Vec {ℓ} = Σ (Set ℓ) (λ - → Nat)

postulate Id-Type-Vec : (A A' : Set ℓ) (n n' : Nat) →
                       Id (Set ℓ) (Vec A n) (Vec A' n') ≡
                       Id telescope-Vec (A , n) (A' , n') 

{-# REWRITE Id-Type-Vec #-}

postulate Id-vector-vnil-vnil : (A : Set ℓ) →
                            Id (Vec A 0) [] [] ≡ ⊤P

-- postulate Id-vector-vnil-vcons : not well typed
-- postulate Id-vector-vcons-vnil : not well typed

{- Note that the rule below are technically non-linear, but the arguments A and n of vcons can be seen as "forced" -}

postulate Id-vector-vcons-vcons : (A : Set ℓ) (n : Nat) (a a' : A)
                                  (l l' : Vec {ℓ} A n) →
                                  Id {ℓ} (Vec {ℓ} A (suc n)) (_∷_ {A = A} {n = n} a l) (_∷_ {A = A} {n = n} a' l') ≡
                                  Id A a a' × Id (Vec A n) l l'

{-# REWRITE Id-vector-vnil-vnil #-}
{-# REWRITE Id-vector-vcons-vcons #-}


postulate cast-Vec-vnil : (A A' : Set ℓ) (e : _) →
                       cast {ℓ} (Vec {ℓ} A 0) (Vec {ℓ} A' 0) e [] ≡ []

postulate cast-Vec-vcons : (A A' : Set ℓ) (n n' : Nat) (a : A) (v : Vec {ℓ} A n) (e : _) →
                       cast {ℓ} (Vec {ℓ} A (suc n)) (Vec {ℓ} A' (suc n')) e (_∷_ {A = A} {n = n} a v) ≡
                       _∷_ {A = A'} {n = n'} (cast {ℓ} A A' (fstC e) a) (cast {ℓ} (Vec {ℓ} A n) (Vec {ℓ} A' n') e v)


{-# REWRITE cast-Vec-vnil #-}
{-# REWRITE cast-Vec-vcons #-}


-- Test with weird vectors indexed by lists.

data VecL (A : Set ℓ) (a : A) : List A → Set ℓ where
  []  : VecL A a []
  _∷_ : {l : List {ℓ} A} → A → VecL {ℓ} A a l → VecL {ℓ} A a (a ∷ l)

telescope-VecL : Set (lsuc ℓ)
telescope-VecL {ℓ} = Σ (Set ℓ) (λ A → Σ A (λ - → List A))

postulate Id-vectorL-vnil-vnil : (A : Set ℓ) (a : A) →
                            Id (VecL A a []) [] [] ≡ ⊤P

-- postulate Id-vector-vnil-vcons : not well typed
-- postulate Id-vector-vcons-vnil : not well typed

postulate Id-vectorL-vcons-vcons : (A : Set ℓ) (x : A) (l : List {ℓ} A) (a a' : A)
                                  (v v' : VecL {ℓ} A x l) →
                                  Id (VecL {ℓ} A x (x ∷ l)) (a ∷ v) (a' ∷ v') ≡
                                  Id A a a' × Id (VecL {ℓ} A x l) v v'

{-# REWRITE Id-vectorL-vnil-vnil #-}
{-# REWRITE Id-vectorL-vcons-vcons #-}

postulate Id-Type-VecL : (A A' : Set ℓ) (a : A) (a' : A') (l : List {ℓ} A) (l' : List {ℓ} A') →
                       Id (Set ℓ) (VecL {ℓ} A a l) (VecL {ℓ} A' a' l') ≡
                       Id telescope-VecL (A , (a , l)) (A' , (a' , l'))

{-# REWRITE Id-Type-VecL #-}

postulate cast-VecL-vnil : (A A' : Set ℓ) (a : A) (a' : A')  (e : _) →
                       cast {ℓ} (VecL {ℓ} A a []) (VecL {ℓ} A' a' []) e [] ≡ []

postulate cast-VecL-vcons : (A A' : Set ℓ) (a : A) (a' : A') (l : List {ℓ} A) (l' : List {ℓ} A') 
                           (x : A) (v : VecL {ℓ} A a l) (x' : A') (v' : VecL {ℓ} A' a' l') (e : _) →
                     cast {ℓ} (VecL {ℓ} A a (a ∷ l)) (VecL {ℓ} A' a' (a' ∷ l')) e (x ∷ v) ≡ 
                     cast {ℓ} A A' (fstC e) a ∷ cast {ℓ} (VecL {ℓ} A a l) (VecL {ℓ} A' a' l') ( fstC e , (fstC (sndC e) , sndC (sndC (sndC e)))) v 


{-# REWRITE cast-VecL-vnil #-}
{-# REWRITE cast-VecL-vcons #-}

-- Now for Path

telescope-Path : Set (lsuc ℓ)
telescope-Path {ℓ} = Σ (Set ℓ) (λ A → Σ A (λ - → A))

postulate Id-Path : (A : Set ℓ) (x : A) (y : A) (e e' : _)→
                    Id (x ≡ y) e e' ≡ ⊤P

{-# REWRITE Id-Path #-}

postulate Id-Type-Path : (A A' : Set ℓ) (x y : A) (x' y' : A') →
                       Id (Set ℓ) (x ≡ y) (x' ≡ y') ≡
                       Id (Prop ℓ) (Id A x y) (Id A' x' y') 

{-# REWRITE Id-Type-Path #-}

-- not enough to get canonicity

-- postulate cast-Path : (A A' : Set ℓ) (x : A) (x' : A') (e : _) →
--                     cast (x ≡ x) (x' ≡ x') e refl ≡ refl

-- {-# REWRITE cast-Path #-}

transport-Path : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : x ≡ y) → P y
transport-Path P x t y refl = t

transport-Path-prop : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : x ≡ y) → P y
transport-Path-prop P x t y refl = t

id-to-Path : {A : Set ℓ} {x y : A} → Id A x y → x ≡ y
id-to-Path {ℓ} {A} {x} {y} = transport-Id {ℓ} (λ y → x ≡ y) x (refl) y 

path-to-Id : {A : Set ℓ} {x y : A} → x ≡ y → Id A x y 
path-to-Id {ℓ} {A} {x} {y} = transport-Path-prop {ℓ} {ℓ} (Id {ℓ} A x) x (Id-refl {ℓ} x) y

-- we treat cast X (a ≡ b) e x as a new constructor of equality

postulate transport-Path-cast : {A X : Set ℓ} (P : A → Set ℓ₁) (a : A) (t : P a) (b : A) (x : X) (e : Id {lsuc ℓ} (Set ℓ) X ( _≡_ {ℓ} a b)) → P b →
                             transport-Path {ℓ} {ℓ₁} P a t b (cast {ℓ} X (a ≡ b) e x) ≡
                             transport-Id {ℓ} {ℓ₁} P a t b (path-to-Id {ℓ} (cast {ℓ} X (a ≡ b) e x))

{-# REWRITE transport-Path-cast #-}

transport-refl-Path : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) → transport-Path P x t x refl ≡ t
transport-refl-Path P x t = refl

transport-refl-Path' : {A X : Set ℓ} (P : A → Set ℓ₁) (a : A) (t : P a) (x : X) (e : _) →
                       Id {ℓ₁} (P a) (transport-Path {ℓ} {ℓ₁} P a t a (cast {ℓ} X ( _≡_ {ℓ} a a) e x)) t
transport-refl-Path' {ℓ} {ℓ₁} {A} {X} P a t x e = transport-refl {ℓ} {ℓ₁} P a t (Id-refl {ℓ = ℓ} a) 

funext-Path : (A : Set ℓ) (B : A → Set ℓ₁) (f g : (a : A) → B a) →
          ((a : A) → f a ≡ g a) → f ≡ g 
funext-Path A B f g e = id-to-Path (λ a → path-to-Id (e a))

etaBool : (a : Bool) → a ≡ (if a then true else false)
etaBool true = refl
etaBool false = refl

eq_fun : (λ (b : Bool) → b) ≡ (λ (b : Bool) → if b then true else false)
eq_fun = funext-Path Bool (λ - → Bool) _ _ λ a → etaBool a

-- standard boolean using equality

std-bool : Bool
std-bool = transport-Path (λ f → Bool) (λ (b : Bool) → b) true (λ (b : Bool) → if b then true else false) eq_fun


