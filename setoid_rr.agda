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

open i public

{- 
 Axiomatisation of Id, Id-refl, transport and transport-refl (propositionally)

 Note that Id-refl, transport-Prop and transport-refl are axioms in Prop, 
 so we don't need to give them a computation content. 

 Also transport-refl is useless for transport on Prop
-}

postulate Id : (A : Set ℓ) → A → A → Prop ℓ

postulate Id-refl : {A : Set ℓ} (x : A) → Id A x x

postulate transport-prop : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

ap : {A : Set ℓ} {B : Set ℓ₁} {x y : A} (f : A → B) (e : Id A x y) →
     Id B (f x) (f y)
ap {ℓ} {ℓ₁} {A} {B} {x} {y} f e = transport-prop (λ z → Id B (f x) (f z)) x (Id-refl _) y e

postulate cast : (A B : Set ℓ) (e : Id (Set ℓ) A B) → A → B 

postulate cast-refl : {A : Set ℓ} (e : Id _ A A) (a : A) → Id A (cast A A e a) a

transport : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y
transport P x t y e = cast (P x) (P y) (ap P e) t

transport-refl : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (e : Id A x x) → Id (P x) (transport P x t x e) t
transport-refl P x t e = cast-refl (ap P e) t

-- direct derived functions 

inverse  : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) → Id A y x
inverse{ℓ} A {x} {y} p = transport-prop (λ z → Id A z x) x (Id-refl x) y p

concatId : (A : Set ℓ) {x y z : A} (p : Id {ℓ} A x y)
         (q : Id {ℓ} A y z)→ Id A x z
concatId A {x} {y} {z} p q = transport-prop (λ t → Id A x t) y p z q



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


postulate Id-set : Id (Set (lsuc ℓ₁)) (Set ℓ₁) (Set ℓ₁) ≡ ⊤P

{-# REWRITE Id-set #-}

--- Contractibility of singletons and J can be defined

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

cast-inv : (A B : Set ℓ) (e : Id _ A B) (a : A) →
                     Id A (cast B A (inverse (Set ℓ) {x = A} {y = B} e) (cast A B e a)) a
cast-inv {ℓ} A B e a = let e-refl = cast-refl (Id-refl A) a in
                       let e-refl-cast = cast-refl (Id-refl A) (cast A A (Id-refl A) a) in
                       J-prop (Set ℓ) A (λ B e → Id A (cast B A (inverse (Set ℓ) {x = A} {y = B} e) (cast A B e a)) a)
                              (concatId A e-refl-cast e-refl) B e

postulate cast-set : (A : Set ℓ) (e : _) → cast (Set ℓ) (Set ℓ) e A ≡ A

{-# REWRITE cast-set #-}

postulate cast-prop : (A : Prop ℓ) (e : _) → cast (Prop ℓ) (Prop ℓ) e A ≡ A

{-# REWRITE cast-prop #-}

postulate cast-Pi-nodep : (A A' : Set ℓ) (f : (a : A) → Set ℓ₁) (e : _) →
                    cast ((a : A) → Set ℓ₁) ((a' : A') → Set ℓ₁) e f ≡
                    λ (a' : A') → let a = cast A' A (inverse (Set ℓ) {x = A} {y = A'} (fstC e)) a' in f a 

{-# REWRITE cast-Pi-nodep #-}

postulate cast-Pi : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (f : (a : A) → B a) (e : Id _ ((a : A) → B a) ((a' : A') → B' a')) →
                    cast ((a : A) → B a) ((a' : A') → B' a') e f ≡
                    λ (a' : A') → let a = cast A' A (inverse (Set ℓ) {x = A} {y = A'} (fstC e)) a' in
                                  cast _ _ (sndC e a') (f a)

{-# REWRITE cast-Pi #-}

postulate cast-Sigma : (A A' : Set ℓ) (B : A → Set ℓ₁) (B' : A' → Set ℓ₁) (x : A) (y : B x) (e : _) →
                    let eA = fstC e in
                    let x' = cast A A' eA x in 
                    let eB = sndC e x' in
                    let proof = concatId _ {x = B x} (ap B (inverse A (cast-inv A A' eA x))) eB in
                    cast (Σ A B) (Σ A' B') e (x , y) ≡
                    (cast A A' (fstC e) x , cast (B x) (B' x') proof y)


{-# REWRITE cast-Sigma #-}

 
postulate cast-List-nil : (A A' : Set ℓ) (e : _) →
                          cast (List A) (List A') e [] ≡ []

postulate cast-List-cons : (A A' : Set ℓ) (e : _) (a : A) (l : List A) →
                           cast (List A) (List A') e (a ∷ l) ≡
                           cast A A' e a ∷ cast _ _ e l

{-# REWRITE cast-List-nil #-}

{-# REWRITE cast-List-cons #-}


postulate cast-Nat-zero : (e : _) → cast Nat Nat e 0 ≡ 0

postulate cast-Nat-suc : (e : _) (n : Nat ) →
                          cast Nat Nat e (suc n) ≡
                          suc (cast _ _ e n)

{-# REWRITE cast-Nat-zero #-}

{-# REWRITE cast-Nat-suc #-}

postulate cast-Bool-true : (e : _) → cast Bool Bool e true ≡ true

{-# REWRITE cast-Bool-true #-}

postulate cast-Bool-false : (e : _) → cast Bool Bool e false ≡ false

{-# REWRITE cast-Bool-false #-}

postulate cast-Unit : (e : _) → cast ⊤ ⊤ e tt ≡ tt

{-# REWRITE cast-Unit #-}


postulate cast-Box : (A A' : Prop ℓ) (a : A) (f : _) (g : _) →
                    cast (Box A) (Box A') (f , g) (box a) ≡ box (uninj f a)

{-# REWRITE cast-Box #-}

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
                cast (Quotient A R r s t) (Quotient A' R' r' s' t') e (pi A R r s t a) ≡
                pi A' R' r' s' t' (cast A A' (fstC e) a)

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

{- Note that the rule above is technically non-linear, but the arguments A and n of vcons can be seen as "type-forced" -}

postulate cast-Vec-vnil : (A A' : Set ℓ) (e : _) →
                       cast (Vec A 0) (Vec A' 0) e [] ≡ []

postulate cast-Vec-vcons : (A A' : Set ℓ) (n n' : Nat) (a : A) (v : Vec A n) (e : _) →
                       cast (Vec A (suc n)) (Vec A' (suc n')) e (a ∷ v) ≡ cast A A' (fstC e) a ∷ cast (Vec A n) (Vec A' n') e v 


{-# REWRITE cast-Vec-vnil #-}
{-# REWRITE cast-Vec-vcons #-}

{-
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
-}

-- Now for Path

telescope-Path : Set (lsuc ℓ)
telescope-Path {ℓ} = Σ (Set ℓ) (λ A → Σ A (λ - → A))

postulate Id-Path : (A : Set ℓ) (x : A) →
                    Id (x ≡ {- ! -} x) (refl) (refl) ≡ ⊤P


{-# REWRITE Id-Path #-}

postulate Id-Type-Path : (A A' : Set ℓ) (x y : A) (x' y' : A') →
                       Id (Set ℓ) (x ≡ y) (x' ≡ y') ≡
                       Id (Prop ℓ) (Id A x y) (Id A' x' y') -- (A , (x , y)) (A' , (x' , y'))

{-# REWRITE Id-Type-Path #-}

-- not enough to get canonicity

postulate cast-Path : (A A' : Set ℓ) (x : A) (x' : A') (e : _) →
                    cast (x ≡ x) (x' ≡ x') e refl ≡
                    refl

-- {-# REWRITE cast-Path #-}

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

-- non-standard boolean using Path

test' : Bool
test' = transportEq (λ f → Bool) (λ (b : Bool) → b) true (λ (b : Bool) → if b then true else false) test 

Path : (A : Set ℓ) (x : A) (y : A) → Set ℓ
Path A x y = Box (Id A x y)

Path-refl : (A : Set ℓ) (x : A) → Path A x x
Path-refl A x = box (Id-refl x)

transportPath : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : Path A x y) → P y
transportPath P x t y (box e) = cast (P x) (P y) (ap P e) t

transportPath-refl : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) →
                     Id _ (transportPath P x t x (Path-refl A x)) t
transportPath-refl P x t = cast-refl (ap P (Id-refl x)) t
