From Theories Require Import category.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(* Notation "α ⋅ x" := (fun r β => x r (α ∘ β)) (at level 40). *)

(* This is still work in progress *)

Definition falso@{i} : forall X : Type@{i}, X.
Admitted.

(* Type of strict presheaves *)

Record Psh@{i} : Type :=
mkPsh {
  psh0 : forall p : ℙ, Type@{i};
  psh1 : forall p : ℙ, (forall q (α : q ≤ p), psh0 q) -> SProp;
}.

(* Sections at level p *)

Record El@{i} (p : ℙ) (f : Psh@{i}) : Type :=
mkEl {
  el0 : forall q (α : q ≤ p), f.(psh0) q;
  el1 : forall q (α : q ≤ p), f.(psh1) q (α · el0);
}.

(* Type of fibrant strict presheaves over yoneda(p) *)

Record yft@{i} (p : ℙ) := mkYFT {
  yft0 : forall q (α : q ≤ p), Type@{i};
  yft1 : forall q (α : q ≤ p), (forall r (β : r ≤ q), yft0 r (α ∘ β)) -> SProp;
  fibstruct : sTrue; (** TODO **)
}.

Arguments yft0 {_}.
Arguments yft1 {_}.
Arguments fibstruct {_}.

Definition yft_funct@{i} {p q : ℙ} (α : q ≤ p) :
  yft@{i} p -> yft@{i} q :=
fun f =>
{|
  yft0 := α · yft0 f;
  yft1 := fun r β s => yft1 f r (α ∘ β) s;
  fibstruct := sI  (** TODO **)
|}.

Definition yftR@{i j} {p : ℙ} (s : forall q : nat, q ≤ p -> yft@{i} q) : SProp :=
forall q (α : q ≤ p),
seq@{j} (s q α) (yft_funct@{i} α (s p !)).

Definition cast0 {p : ℙ}
  (A0 : forall q (α : q ≤ p), yft q)
  (A1 : forall q (α : q ≤ p), yftR (α · A0))
  {q} (α : q ≤ p) {r} (β : r ≤ q) :
  (A0 r (α ∘ β)).(yft0) r ! -> (A0 q α).(yft0) r β.
Proof.
refine (fun x => _).
refine (J_seq (yft r) (A0 r (α ∘ β)) (fun a _ => a.(yft0) r !) x _ (A1 q α r β)).
Defined.

(* There is an analogue cast1 for parametricity predicates. *)
(* will write if needed *)

(* Universe of fibrant types *)

Definition Uᶠ@{i j k} : Psh@{j} :=
mkPsh@{j} yft@{i} (fun p s => yftR@{i k} s).

(* Uᶠ is an element of Uᶠ *)

Definition U0 (p : ℙ) : psh0 Uᶠ p.
Proof.
unshelve econstructor.
- exact (fun q α => yft q).
- refine (fun q α s => yftR s).
- easy. (** TODO **)
Defined.

Definition U1 (p : ℙ) : psh1 Uᶠ p (fun q α => U0 q).
Proof.
unshelve refine (fun q α => _).
reflexivity.
Defined.

(* Now that we have this, everything should be constrained *)
(* Let us write a translation in the style of PMP *)

Definition El0 {p : ℙ}
  (A0 : forall q (α : q ≤ p), psh0 Uᶠ q) : Type.
Proof.
exact (forall q (α : q ≤ p), (A0 q α).(yft0) q !).
Defined.

Definition El1 {p : ℙ}
  (A0 : forall q (α : q ≤ p), psh0 Uᶠ q)
  (A1 : forall q (α : q ≤ p), psh1 Uᶠ q (α · A0))
  (x0 : El0 A0) : SProp.
Proof.
unshelve refine (forall q (α : q ≤ p), (A0 q α).(yft1) q ! _).
unshelve refine (fun r β => cast0 A0 A1 α β _).
exact (x0 r (α ∘ β)).
Defined.

(* Translation of Type *)

Definition Type0 {p : ℙ} :
  @El0 p (fun q α => U0 q).
Proof.
  refine (fun q α => U0 q).
Defined.

Definition Type1 {p : ℙ} :
  @El1 p (fun q α => U0 q) (fun q α => U1 q) Type0.
Proof.
  refine (fun q α => U1 q).
Defined.

(* From these definition, it is quite clear that
   * Type0 p : El0 p (Type0 p)
   * Type1 p : El1 p (Type0 p) (Type1 p) *)

(* Translation of Arrow types *)

Definition Arr0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0) :
  @El0 p Type0.
Proof.
unshelve refine (fun q α => mkYFT _ _ _ _).
+ unshelve refine (fun r β =>
  forall
  (x0 : El0 (α ∘ β · A0))
  (x1 : El1 (α ∘ β · A0) (α ∘ β · A1) x0)
  ,
  (B0 r (α ∘ β)).(yft0) r !).
+ unshelve refine (fun r β f =>
  forall
  (x0 : El0 (α ∘ β · A0))
  (x1 : El1 (α ∘ β · A0) (α ∘ β · A1) x0)
  ,
  (B0 r (α ∘ β)).(yft1) r ! (fun r' β' => _)).
  unshelve refine (cast0 B0 B1 (α ∘ β) β' _).
  exact (f r' β' (β' · x0) (β' · x1)).
+ easy. (** TODO **)
Defined.

Definition Arr1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0) :
  @El1 p Type0 Type1 (Arr0 A0 A1 B0 B1).
Proof.
unshelve refine (fun q α r β => _).
reflexivity.
Defined.

(* Abstraction rule *)
(* Note the difference with PMP's translation in the arguments of lam1 *)

Definition lam0 {p A0 A1 B0 B1}
  (f0 : forall q (α : q ≤ p) (x0 : El0 (α · A0)) (x1 : El1 (α · A0) (α · A1) x0), El0 (α · B0))
: El0 (Arr0 A0 A1 B0 B1).
Proof.
refine (fun q α x0 x1 => _).
unshelve refine (f0 q α x0 x1 q !).
Defined.

Definition lam1 {p A0 A1 B0 B1}
  (f0 : forall q (α : q ≤ p) (x0 : El0 (α · A0)) (x1 : El1 (α · A0) (α · A1) x0), El0 (α · B0))
  (f1 : forall q (α : q ≤ p) (x0 : El0 (α · A0)) (x1 : El1 (α · A0) (α · A1) x0),
    El1 (α · B0) (α · B1) (fun r (β : r ≤ q) => f0 r (α ∘ β) (β · x0) (β · x1) r !))
: El1 (Arr0 A0 A1 B0 B1) (Arr1 A0 A1 B0 B1) (lam0 f0).
Proof.
refine (fun q α x0 x1 => _).
exact (f1 q α x0 x1 q !).
Defined.

(* Application rule *)

Definition app0 {p A0 A1 B0 B1} (f0 : @El0 p (Arr0 A0 A1 B0 B1)) (x0 : El0 A0) (x1 : El1 A0 A1 x0) : El0 B0.
Proof.
refine (fun q α => f0 q α (α · x0) (α · x1)).
Defined.

Definition app1 {p A0 A1 B0 B1} {f0 : @El0 p (Arr0 A0 A1 B0 B1)}
  (f1 : El1 _ (Arr1 A0 A1 B0 B1) f0) (x0 : El0 A0) (x1 : El1 A0 A1 x0) : El1 B0 B1 (app0 f0 x0 x1).
Proof.
refine (fun q α => f1 _ _ (α · x0) (α · x1)).
Defined.

(* Dependent products *)

Definition Prod0 {p}
  (A0 : @El0 p Type0)
  (A1 : El1 Type0 Type1 A0)
  (B0 : @El0 p (Arr0 A0 A1 Type0 Type1))
  (B1 : El1 (Arr0 A0 A1 Type0 Type1) (Arr1 A0 A1 Type0 Type1) B0)
  : @El0 p Type0.
Proof.
unshelve refine (fun q α => mkYFT _ _ _ _).
+ unshelve refine (fun r β =>
  forall
  (x0 : El0 (α ∘ β · A0))
  (x1 : El1 (α ∘ β · A0) (α ∘ β · A1) x0)
  ,
  (B0 r (α ∘ β) x0 x1).(yft0) r !).
+ unshelve refine (fun r β f0 =>
  forall
  (x0 : El0 (α ∘ β · A0))
  (x1 : El1 (α ∘ β · A0) (α ∘ β · A1) x0)
  ,
  (B0 r (α ∘ β) x0 x1).(yft1) r ! (fun r2 β2 => _)).
  unshelve refine (@cast0 r
    (fun r3 (β3 : r3 ≤ r) => B0 r3 (α ∘ β ∘ β3) (β3 · x0) (β3 · x1))
    (fun r3 (β3 : r3 ≤ r) => B1 r3 (α ∘ β ∘ β3) (β3 · x0) (β3 · x1))
    _ ! _ β2 (f0 r2 _ (β2 · x0) (β2 · x1))).
+ easy. (** TODO **)
Defined.

Definition Prod1 {p}
  (A0 : @El0 p Type0)
  (A1 : El1 Type0 Type1 A0)
  (B0 : El0 (Arr0 A0 A1 Type0 Type1))
  (B1 : El1 (Arr0 A0 A1 Type0 Type1) (Arr1 A0 A1 Type0 Type1) B0)
  : El1 Type0 Type1 (Prod0 A0 A1 B0 B1).
Proof.
refine (fun q α r β => _).
reflexivity.
Defined.

(* Dependent abstraction *)

Definition dlam0 {p : ℙ}
  {A0 A1}
  {B0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {B1 : @El1 p (Arr0 A0 A1 Type0 Type1) (Arr1 A0 A1 Type0 Type1) B0}
  (f0 : forall q (α : q ≤ p) (x0 : El0 (α · A0))
        (x1 : El1 (α · A0) (α · A1) x0),
        @El0 q (@app0 _ _ _ _ Type1 (α · B0) x0 x1))
  : El0 (Prod0 A0 A1 B0 B1).
Proof.
refine (fun q α x0 x1 => f0 q α x0 x1 q !).
Defined.

Definition dlam1 {p}
  {A0 A1}
  {B0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {B1 : @El1 p (Arr0 A0 A1 Type0 Type1) (Arr1 A0 A1 Type0 Type1) B0}
  {f0 : forall q (α : q ≤ p) (x0 : El0 (α · A0)) (x1 : El1 (α · A0) (α · A1) x0), El0 (@app0 _ _ _ _ Type1 (α · B0) x0 x1)}
  (f1 : forall q (α : q ≤ p) (x0 : El0 (α · A0)) (x1 : El1 (α · A0) (α · A1) x0),
    El1 (@app0 _ _ _ _ Type1 (α · B0) x0 x1)
        (@app1 q (α · A0) (α · A1) (α · Type0) (α · Type1) (α · B0) (α · B1) x0 x1)
        (fun r (β : r ≤ q) => f0 r (α ∘ β) (β · x0) (β · x1) r !))
  : El1 (Prod0 A0 A1 B0 B1) (Prod1 A0 A1 B0 B1) (dlam0 f0).
Proof.
refine (fun q α x0 x1 => f1 q α x0 x1 q !).
Defined.

(* Dependent application *)

Definition dapp0 {p}
  {A0 A1}
  {B0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {B1 : El1 (Arr0 A0 A1 Type0 Type1) (Arr1 A0 A1 Type0 Type1) B0}
  (f0 : El0 (Prod0 A0 A1 B0 B1))
  (x0 : El0 A0) (x1 : El1 A0 A1 x0) :
  @El0 p (app0 B0 x0 x1).
Proof.
  intros q α.
  exact (f0 q α (α · x0) (α · x1)).
Defined.

Definition dapp1 {p}
  {A0 A1}
  {B0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {B1 : El1 (Arr0 A0 A1 Type0 Type1) (Arr1 A0 A1 Type0 Type1) B0}
  (f0 : El0 (Prod0 A0 A1 B0 B1))
  (f1 : El1 _ (Prod1 A0 A1 B0 B1) f0)
  (x0 : El0 A0) (x1 : El1 A0 A1 x0) :
  El1 (app0 B0 x0 x1) (app1 B1 x0 x1) (@dapp0 p A0 A1 B0 B1 f0 x0 x1).
Proof.
  intros q α.
  exact (f1 q α (α · x0) (α · x1)).
Defined.

(* Translation of bool *)

Inductive boolR {p} : (forall q (α : q ≤ p), bool) -> SProp :=
| boolr : forall (b : bool), boolR (fun q α => b).

Definition bool0 {p} : @El0 p Type0.
Proof.
unshelve refine (fun q α => mkYFT _ _ _ _).
+ unshelve refine (fun r β => bool).
+ unshelve refine (fun r β s => boolR s).
+ easy. (** TODO **)
Defined.

Definition bool1 {p} : @El1 p Type0 Type1 bool0.
Proof.
unshelve refine (fun q α r β => _).
reflexivity.
Defined.

Definition true0 {p} : @El0 p bool0.
Proof.
unshelve refine (fun q α => true).
Defined.

Definition true1 {p} : @El1 p bool0 bool1 true0.
Proof.
unshelve refine (fun q α => _).
exact (boolr true).
Defined.

(* etc etc *)
