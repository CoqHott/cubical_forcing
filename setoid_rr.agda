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
 Axiomatisation of Id, Id_refl, transport and transport_refl (propositionally)

 Note that Id_refl, transport_Prop and transport_refl are axioms in Prop, 
 so we don't need to give them a computation content. 

 Also transport_refl is useless for transport on Prop
-}

postulate Id : (A : Set ℓ) → A → A → Prop ℓ

postulate Id_refl : {A : Set ℓ} (x : A) → Id A x x

postulate transport : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

postulate transport_prop : {A : Set ℓ} (P : A → Prop ℓ₁) (x : A) (t : P x) (y : A) (e : Id A x y) → P y

postulate transport_refl : {A : Set ℓ} (P : A → Set ℓ₁) (x : A) (t : P x) (e : Id A x x) → Id (P x) (transport P x t x e) t

-- direct derived functions 

inverse : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) → Id A y x
inverse A {x} {y} p = transport_prop (λ z → Id A z x) x (Id_refl x) y p

trans : (A : Set ℓ) {x y z : A} (p : Id {ℓ} A x y)
         (q : Id {ℓ} A y z)→ Id A x z
trans A {x} {y} {z} p q = transport_prop (λ t → Id A x t) y p z q

ap : (A : Set ℓ) (B : Set ℓ₁) (f : A → B) (x y : A) (e : Id A x y) →
     Id B (f x) (f y)
ap A B f x y e = transport_prop (λ z → Id B (f x) (f z)) x (Id_refl _) y e

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


postulate Id_Sigma : (A : Set ℓ) (B : A → Set ℓ₁) (a a' : A)
                     (b : B a) (b' : B a') → 
                     Id (Σ A B) (a , b) (a' , b') ≡
                     Tel (Id A a a')
                         (λ e → Id (B a') (transport B a b a' e) b')

{-# REWRITE Id_Sigma #-}

postulate Id_Box : (A : Prop ℓ) (p q : Box A) → Id (Box A) p q ≡ ⊤P

{-# REWRITE Id_Box #-}

postulate Id_Unit : (p q : ⊤) → Id ⊤ p q ≡ ⊤P

{-# REWRITE Id_Unit #-}

postulate Id_list_nil_nil : (A : Set ℓ) →
                            Id (List A) [] [] ≡ ⊤P

postulate Id_list_nil_cons : (A : Set ℓ) (a' : A) (l' : List A) →
                             Id (List A) [] (a' ∷ l') ≡ i ⊥

postulate Id_list_cons_nil : (A : Set ℓ) (a : A) (l : List A) →
                             Id (List A) (a ∷ l) [] ≡ i ⊥

postulate Id_list_cons_cons : (A : Set ℓ) (a a' : A) (l l' : List A) →
                             Id (List A) (a ∷ l) (a' ∷ l') ≡
                             Id A a a' × Id (List A) l l'

{-# REWRITE Id_list_nil_nil #-}
{-# REWRITE Id_list_nil_cons #-}
{-# REWRITE Id_list_cons_nil #-}
{-# REWRITE Id_list_cons_cons #-}

postulate Id_nat_zero_zero : Id Nat 0 0 ≡ ⊤P

postulate Id_nat_zero_suc : (n : Nat) →
                            Id Nat 0 (suc n) ≡ i ⊥

postulate Id_nat_suc_zero : (n : Nat) →
                            Id Nat (suc n) zero ≡ i ⊥

postulate Id_nat_suc_suc : (n n' : Nat) →
                           Id Nat (suc n) (suc n') ≡
                           Id Nat n n'

{-# REWRITE Id_nat_zero_zero #-}
{-# REWRITE Id_nat_zero_suc #-}
{-# REWRITE Id_nat_suc_zero #-}
{-# REWRITE Id_nat_suc_suc #-}

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

postulate Id_Type_Unit : Id Set ⊤ ⊤ ≡ ⊤P
                        
{-# REWRITE Id_Type_Unit #-}

postulate Id_Type_Nat : Id Set Nat Nat ≡ Id Set ⊤ ⊤
                        
{-# REWRITE Id_Type_Nat #-}

-- rewrite rules for the identity type on Prop : Prop ext modulo cumul 

postulate Id_prop : (P Q : Prop ℓ) → Id (Prop ℓ) P Q ≡ i (P → Q) × (Q → P)

{-# REWRITE Id_prop #-}

-- Contractibility of singletons and J can be defined

contr_sing : (A : Set ℓ) {x y : A} (p : Id {ℓ} A x y) →
    Id (Σ A (λ y → Box (Id A x y))) (x , box (Id_refl x)) (y , box p) 
contr_sing A {x} {y} p = p , ttP

J : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Set ℓ₁) 
    (t : P x (Id_refl x)) (y : A) (e : Id A x y) → P y e
J A x P t y e = transport (λ z → P (fst z) (unbox (snd z))) (x , box (Id_refl x)) t (y , box e) (contr_sing A e)

J_prop : (A : Set ℓ) (x : A) (P : (y : A) → Id A x y → Prop ℓ₁) 
    (t : P x (Id_refl x)) (y : A) (e : Id A x y) → P y e
J_prop A x P t y e = transport_prop (λ z → P (fst z) (unbox (snd z))) (x , box (Id_refl x)) t (y , box e) (contr_sing A e)

-- tranporting back and forth is the identity

transport_inv : (X : Set ℓ) (A : X → Set ℓ₁) 
                (x : X) (y : X) (e : Id X x y) (a : A x) →
    Id (A x) (transport A y (transport A x a y e) x (inverse X e)) a
transport_inv X A x y e a = let e_refl = transport_refl A x a (Id_refl x)
                                e_refl_inv = inverse (A x) e_refl
                            in J_prop X x (λ y e → Id (A x) (transport A y (transport A x a y e) x (inverse X e)) a) (transport_prop (λ Z → Id (A x) (transport A x Z x (Id_refl x)) a) a e_refl _ e_refl_inv) y e

-- we can now state rewrite rules for transports

postulate transport_Pi : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                         (x : X) (f : (a : A x) → B x a) (y : X) (e : Id X x y) →
                         transport (λ x → (a : A x) → B x a) x f y e ≡
                         λ (a' : A y) → let a = transport A y a' x (inverse X e)
                                        in transport (λ z → B (fst z) (snd z)) (x , a) (f a) (y , a')
                                                     (e , transport_inv X A y x (inverse X e) a') 

{-# REWRITE transport_Pi #-}

postulate transport_Sigma : (X : Set ℓ) (A : X → Set ℓ₁) (B : (x : X) → A x → Set ℓ₂)
                            (x : X) (a : A x) (b : B x a) (y : X) (e : Id X x y) →
                            transport (λ z → Σ (A z) (B z)) x (a , b) y e ≡
                            (transport A x a y e , transport (λ z → B (fst z) (snd z)) _ b _ (e , Id_refl (transport A x a y e)))

{-# REWRITE transport_Sigma #-}

postulate transport_Unit : (X : Set ℓ) (x : X) (y : X) (e : Id X x y) →
                           transport (λ x → ⊤) x tt y e ≡ tt

{-# REWRITE transport_Unit #-}

postulate transport_List_nil : (X : Set ℓ) (A : X → Set ℓ₁) (x : X) (y : X) (e : Id X x y) →
                               transport (λ x → List (A x)) x [] y e ≡ []

postulate transport_List_cons : (X : Set ℓ) (A : X → Set ℓ₁) (x : X) (a : A x) (l : List (A x))
                                (y : X) (e : Id X x y) →
                                transport (λ x → List (A x)) x (a ∷ l) y e ≡
                                transport A x a y e ∷ transport (λ x → List (A x)) x l y e

{-# REWRITE transport_List_nil #-}
{-# REWRITE transport_List_cons #-}

postulate transport_nat_zero : (X : Set ℓ) (x : X) (y : X) (e : Id X x y) →
                               transport (λ x → Nat) x 0 y e ≡ 0

postulate transport_nat_suc : (X : Set ℓ) (x : X) (n : Nat)
                              (y : X) (e : Id X x y) →
                              transport (λ x → Nat) x (suc n) y e ≡
                              suc (transport (λ x → Nat) x n y e)

{-# REWRITE transport_nat_zero #-}
{-# REWRITE transport_nat_suc #-}

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

postulate cast_Nat : (n : Nat) (e : _) →
                    transport (λ T → T) Nat n Nat e ≡
                    transport (λ T → Nat) ⊤ n ⊤ e

{-# REWRITE cast_Nat #-}

postulate transport_on_prop : (X : Set ℓ) (x : X) (P : Prop ℓ₁) (y : X) (e : Id X x y) →
                              transport (λ x → Prop ℓ₁) x P y e ≡ P
{-# REWRITE transport_on_prop #-}

-- sanity check on closed terms

test_J_refl_on_closed_term : (X : Set ℓ) (x : X) →
       transport (λ z → Σ ⊤ (λ z → ⊤)) x (tt , tt) x (Id_refl x) ≡ (tt , tt)
test_J_refl_on_closed_term X x = refl 

-- Quotient types

{- 
  Note that r s and t are not used in the definitions, they are just here
  to make sure the theory stays consistent, because postulating the quotient, 
  we can derive them. In particular, with R = λ _ _ → ⊥, we would get
  a direct inconsistency using Id_refl
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

telescope_Quotient : Set (lsuc ℓ)
telescope_Quotient {ℓ} = Σ (Set ℓ) (λ A →
                         Σ (A → A → Prop ℓ) (λ R → Box (
                         Tel ((x : A) → R x x) (λ r →
                         Tel ((x y : A) → R x y → R y x) (λ s →
                         (x y z : A) → R x y → R y z → R x z)))))

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

postulate Quotient_elim_red : (A : Set ℓ)
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

{-# REWRITE Quotient_elim_red #-}

postulate Quotient_elim_prop : (A : Set ℓ)
               (R : A → A → Prop ℓ)
               (r : (x : A) → R x x)
               (s : (x y : A) → R x y → R y x)
               (t : (x y z : A) → R x y → R y z → R x z)
               (P : Quotient A R r s t → Prop ℓ₁) 
               (p : (x : A) → P (pi A R r s t x))
               (w : Quotient A R r s t) → P w

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
                Id telescope_Quotient 
                   (A , (R , box (r , (s , t))))
                   (A' , (R' , box (r' , (s' , t'))))

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
                transport (λ (X : telescope_Quotient)
                                  → let struct = unbox (snd (snd X))
                                    in Quotient (fst X) (fst (snd X))
                                                (fstC struct)
                                                (fstC (sndC struct))
                                                (sndC (sndC struct)))
                          (A , (R , box (r , (s , t))))
                          q
                          (A' , (R' , box (r' , (s' , t'))))
                          e

{-# REWRITE cast_Quotient #-}

-- Sanity Check: transport_refl oon quotient type

transport_refl_Quotient : (X : Set ℓ)
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
transport_refl_Quotient X A R r s t x q e =
  Quotient_elim_prop (A x) (R x) (r x) (s x) (t x)
                     ((λ a → Id _ (transport (λ (x : X) → Quotient (A x) (R x) (r x) (s x) (t x)) x a x e) a))
                     (λ a → transport_prop (λ a' → R x a' a) a (r x a) (transport A x a x e) ((inverse (A x) (transport_refl A x a e)))) q

-- Vector (or how to deal with indices)
-- Some of the rewrite rules below can be defined only because
-- the indexes of vnil and vcons are given by constructor of Nat

telescope_Vec : Set (lsuc ℓ)
telescope_Vec {ℓ} = Σ (Set ℓ) (λ _ → Nat)

postulate Id_vector_vnil_vnil : (A : Set ℓ) →
                            Id (Vec A 0) [] [] ≡ ⊤P

-- postulate Id_vector_vnil_vcons : not well typed
-- postulate Id_vector_vcons_vnil : not well typed

postulate Id_vector_vcons_vcons : (A : Set ℓ) (n : Nat) (a a' : A)
                                  (l l' : Vec A n) →
                                  Id (Vec A (suc n)) (a ∷ l) (a' ∷ l') ≡
                                  Id A a a' × Id (Vec A n) l l'

{-# REWRITE Id_vector_vnil_vnil #-}
{-# REWRITE Id_vector_vcons_vcons #-}

postulate Id_Type_Vec : (A A' : Set ℓ) (n n' : Nat) →
                       Id (Set ℓ) (Vec A n) (Vec A' n') ≡
                       Id telescope_Vec (A , n) (A' , n') 

{-# REWRITE Id_Type_Vec #-}

postulate transport_Vec_vnil : (X : Set ℓ) (A : X → Set ℓ₁)
                                  (x : X) (y : X) (e : Id X x y) →
                       transport (λ x → Vec (A x) 0) x [] y e ≡ []

postulate transport_Vec_vcons : (X : Set ℓ) (A : X → Set ℓ₁) (n : X → Nat)
                                   (x : X) (a : A x) (l : Vec (A x) (n x))
                                   (y : X) (e : Id X x y) →
                       transport (λ (z : X) → Vec (A z) (suc (n z))) x (a ∷ l) y e ≡
                       transport A x a y e ∷ transport (λ z → Vec (A z) (n z)) x l y e

{-# REWRITE transport_Vec_vnil #-}
{-# REWRITE transport_Vec_vcons #-}

postulate cast_Vec : (A A' : Set ℓ) (n n' : Nat) (v : Vec A n) (e : _) →
                    transport (λ T → T) (Vec A n) v (Vec A' n') e ≡
                    transport (λ (X : telescope_Vec) → Vec (fst X) (snd X)) (A , n) v (A' , n') e

{-# REWRITE cast_Vec #-}

-- Test with weird vectors indexed by lists.

data VecL (A : Set ℓ) (a : A) : List A → Set ℓ where
  []  : VecL A a []
  _∷_ : {l : List A} → A → VecL A a l → VecL A a (a ∷ l)

telescope_VecL : Set (lsuc ℓ)
telescope_VecL {ℓ} = Σ (Set ℓ) (λ A → Σ A (λ _ → List A))

postulate Id_vectorL_vnil_vnil : (A : Set ℓ) (a : A) →
                            Id (VecL A a []) [] [] ≡ ⊤P

-- postulate Id_vector_vnil_vcons : not well typed
-- postulate Id_vector_vcons_vnil : not well typed

postulate Id_vectorL_vcons_vcons : (A : Set ℓ) (x : A) (l : List A) (a a' : A)
                                  (v v' : VecL A x l) →
                                  Id (VecL A x (x ∷ l)) (a ∷ v) (a' ∷ v') ≡
                                  Id A a a' × Id (VecL A x l) v v'

{-# REWRITE Id_vectorL_vnil_vnil #-}
{-# REWRITE Id_vectorL_vcons_vcons #-}

postulate Id_Type_VecL : (A A' : Set ℓ) (a : A) (a' : A') (l : List A) (l' : List A') →
                       Id (Set ℓ) (VecL A a l) (VecL A' a' l') ≡
                       Id telescope_VecL (A , (a , l)) (A' , (a' , l'))

{-# REWRITE Id_Type_VecL #-}

postulate transport_VecL_vnil : (X : Set ℓ) (A : X → Set ℓ₁) (Val : (x : X) → A x)
                                (x : X) (y : X) (e : Id X x y) →
                       transport (λ x → VecL (A x) (Val x) []) x [] y e ≡ []

postulate transport_VecL_vcons : (X : Set ℓ) (A : X → Set ℓ₁) (Val : (x : X) → A x) (l : (x : X) → List (A x))
                                   (x : X) (a : A x) (v : VecL (A x) (Val x) (l x))
                                   (y : X) (e : Id X x y) →
                       transport (λ (z : X) → VecL (A z) (Val z) (Val z ∷ l z)) x (a ∷ v) y e ≡
                       transport A x a y e ∷ transport (λ z → VecL (A z) (Val z) (l z)) x v y e

{-# REWRITE transport_VecL_vnil #-}
{-# REWRITE transport_VecL_vcons #-}

postulate cast_VecL : (A A' : Set ℓ) (a : A) (a' : A') (l : List A) (l' : List A') (v : VecL A a l) (e : _) →
                    transport (λ T → T) (VecL A a l) v ( VecL A' a' l') e ≡
                    transport (λ (X : telescope_VecL) → VecL (fst X) (fst (snd X)) (snd (snd X))) (A , (a , l)) v (A' , (a' , l')) e

{-# REWRITE cast_VecL #-}

-- Now for Path

telescope_Path : Set (lsuc ℓ)
telescope_Path {ℓ} = Σ (Set ℓ) (λ A → Σ A (λ _ → A))

postulate Id_Path : (A : Set ℓ) (x y : A) (p q : x ≡ y) →
                    Id (x ≡ y) p q ≡ ⊤P


{-# REWRITE Id_Path #-}

postulate Id_Type_Path : (A A' : Set ℓ) (x y : A) (x' y' : A') →
                       Id (Set ℓ) (x ≡ y) (x' ≡ y') ≡
                       Id telescope_Path (A , (x , y)) (A' , (x' , y'))

{-# REWRITE Id_Type_Path #-}


postulate transport_Path : (X : Set ℓ) (A : X → Set ℓ₁)
                           (a : (x : X) → A x)
                           (x : X) (y : X) (e : Id X x y) →
                           transport (λ x → a x ≡ a x) x (refl) y e ≡
                           refl

-- This rewrite rule is not valid as it is non-linear

{-# REWRITE transport_Path #-}


postulate cast_Path : (A A' : Set ℓ) (x y : A) (x' y' : A') (p : x ≡ y) (e : _) →
                    transport (λ T → T) (x ≡ y) p (x' ≡ y') e ≡
                    transport (λ (X : telescope_Path) → fst (snd X) ≡ snd (snd X))
                              (A , (x , y)) p (A' , (x' , y')) e  

{-# REWRITE cast_Path #-}


