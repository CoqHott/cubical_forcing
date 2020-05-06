From Theories Require Import category.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Notation "α ⋅ x" := (fun r β => x r (α ∘ β)) (at level 40).

(* This is still work in progress *)

Definition falso@{i} : forall X : Type@{i}, X.
Admitted.

Definition sfalso@{i} : forall X : SProp, X.
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

Arguments el0 {_ _}.
Arguments el1 {_ _}.

Definition seq_El {p : ℙ} {f : Psh} {s t : El p f} :
  el0 s ≡ el0 t -> s ≡ t.
Proof.
  intro H.
  unshelve refine (J_seqs _ (el0 s)
    (fun t0 e0 => s ≡ {| el0 := t0 ; el1 := J_seqs _ (el0 s) (fun u0 _ => forall q (α : q ≤ p), f.(psh1) q (α ⋅ u0)) (el1 s) t0 e0 |})
    (srefl _) (el0 t) H).
Defined.

(* Functoriality *)

Definition funct@{i} {p q} {f : Psh@{i}} (α : q ≤ p) :
  El@{i} p f -> El@{i} q f :=
fun s => mkEl q f (α ⋅ s.(el0)) (α ⋅ s.(el1)).

(* Type of strict presheaves over yoneda(p) *)

Record yt@{i} (p : ℙ) := mkYT {
  yt0 : forall q (α : q ≤ p), Type@{i};
  yt1 : forall q (α : q ≤ p), (forall r (β : r ≤ q), yt0 r (α ∘ β)) -> SProp;
}.

Arguments yt0 {_}.
Arguments yt1 {_}.

(* This is a strict presheaf *)

Definition yt_funct@{i} {p q} (α : q ≤ p) (f : yt@{i} p) : yt@{i} q :=
mkYT@{i} q (α ⋅ f.(yt0)) (α ⋅ f.(yt1)).

(* Sections *)

Record ytEl@{i j} {p : ℙ} (f : yt@{i} p) : Type@{j} :=
mkYtEl {
  ytel0 : forall q (α : q ≤ p), f.(yt0) q α;
  ytel1 : forall q (α : q ≤ p), f.(yt1) q α (α · ytel0);
}.

Arguments ytel0 {_ _}.
Arguments ytel1 {_ _}.

Definition seq_ytEl {p : ℙ} {f : yt p} {s t : ytEl f} :
  ytel0 s ≡ ytel0 t -> s ≡ t.
Proof.
  intro H.
  unshelve refine (J_seqs _ (ytel0 s)
    (fun t0 e0 => s ≡ {| ytel0 := t0 ; ytel1 := J_seqs _ (ytel0 s) (fun u0 _ => forall q (α : q ≤ p), f.(yt1) q α (α ⋅ u0)) (ytel1 s) t0 e0 |})
    (srefl _) (ytel0 t) H).
Defined.

Definition ytEl_funct@{i j} {p q} {f : yt@{i} p} (α : q ≤ p) :
  ytEl@{i j} f -> ytEl@{i j} (yt_funct@{i} α f) :=
fun s => mkYtEl@{i j} q (yt_funct α f) (α ⋅ s.(ytel0)) (α ⋅ s.(ytel1)).

(* now let us focus on what is a fibration structure... *)

Definition boxtype@{i j} {p : ℙ} (f : yt@{i} (S p)) :=
  ytEl@{i j} (yt_funct@{i} side_0 f).

Record filler@{i j} {p : ℙ}
  {f : yt@{i} (S p)}
  (t : boxtype@{i j} f) :=
mkFiller {
  fillert : ytEl@{i j} f;
  fillerc : ytEl_funct@{i j} side_0 fillert ≡ t ;
}.

Record fibstruct@{i j} (p : ℙ)
  (f0 : forall q (α : q ≤ p), Type@{i})
  (f1 : forall q (α : q ≤ p) (s : forall r (β : r ≤ q), f0 r (α ∘ β)), SProp)
  : Type@{i} :=
mkFibStruct {
  lift : forall q (α : S q ≤ p)
    (t : boxtype@{i j} (mkYT (S q) (α · f0) (α · f1))),
    filler@{i j} t;
  uniformity : sTrue; (* todo *)
}.

Definition fibstruct_funct@{i j} {p q : ℙ} (α : q ≤ p)
  {f0 : forall q (α : q ≤ p), Type@{i}}
  {f1 : forall q (α : q ≤ p) (s : forall r (β : r ≤ q), f0 r (α ∘ β)), SProp}
  : fibstruct@{i j} p f0 f1 -> fibstruct@{i j} q (α ⋅ f0) (α ⋅ f1).
Proof.
  unshelve refine (fun f => _).
  unshelve refine (mkFibStruct _ _ _ _ _).
  - unshelve refine (fun r β t => _).
    unshelve refine (lift _ _ _ f r (α ∘ β) t).
  - easy. (** todo **)
Defined.

(* Type of fibrant strict presheaves over yoneda(p) *)

Record yft@{i j} (p : ℙ) := mkYFT {
  yft0 : forall q (α : q ≤ p), Type@{i};
  yft1 : forall q (α : q ≤ p), (forall r (β : r ≤ q), yft0 r (α ∘ β)) -> SProp;
  yftfib : fibstruct@{i j} p yft0 yft1;
}.

Arguments yft0 {_}.
Arguments yft1 {_}.
Arguments yftfib {_}.

Definition yft_funct@{i j} {p q : ℙ} (α : q ≤ p) :
  yft@{i j} p -> yft@{i j} q :=
fun f =>
{|
  yft0 := α · yft0 f;
  yft1 := α ⋅ yft1 f;
  yftfib := fibstruct_funct α (yftfib f);
|}.

Definition yftR@{i j k} {p : ℙ} (s : forall q : nat, q ≤ p -> yft@{i j} q) : SProp :=
forall q (α : q ≤ p),
seq@{k} (s q α) (yft_funct@{i j} α (s p !)).

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

Definition Uᶠ@{i j k l} : Psh@{l} :=
mkPsh@{l} yft@{i j} (fun p s => yftR@{i j k} s).

(* Uᶠ is an element of Uᶠ *)

Definition U0 (p : ℙ) : psh0 Uᶠ p.
Proof.
unshelve econstructor.
- exact (fun q α => yft q).
- refine (fun q α s => yftR s).
- unshelve refine (mkFibStruct _ _ _ _ _).
  + unshelve refine (fun q α t => _).
    unshelve refine (mkFiller _ _ _ _ _).
    unshelve refine (mkYtEl _ _ (fun r β => _) (fun r β => _)) ; simpl.
    unshelve refine (ytel0 t r (squish ∘ β)).
    unshelve refine (ytel1 t r (squish ∘ β)).
    reflexivity.
  + easy. (** TODO **)
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

(* Translation of bool *)

Inductive boolR {p} : (forall q (α : q ≤ p), bool) -> SProp :=
| boolr : forall (b : bool), boolR (fun q α => b).

Definition bool0 {p} : @El0 p Type0.
Proof.
unshelve refine (fun q α => mkYFT _ _ _ _).
- unshelve refine (fun r β => bool).
- unshelve refine (fun r β s => boolR s).
- unshelve refine (mkFibStruct _ _ _ _ _).
  + unshelve refine (fun q α t => _).
    unshelve refine (mkFiller _ _ _ _ _).
    unfold boxtype in t. unfold yt_funct in t. simpl in t.
    unshelve refine (mkYtEl _ _ (fun r β => _) (fun r β => _)) ; simpl.
    exact (t.(ytel0) q !).
    exact (boolr (t.(ytel0) q !)).
    apply seq_ytEl. simpl.
    pose proof (ytel1 t q !) as H. simpl in H.
    change (! ⋅ ytel0 t) with (ytel0 t) in H. destruct H.
    reflexivity.
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
+ apply falso.
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

(* Translation of equality *)

Inductive path {p} (A0 : @El0 p Type0) :
  (El0 A0) -> (El0 A0) -> Type :=
| path_c : forall (x : El0 (squish · A0)), path A0 (side_0 · x) (side_1 · x).

Definition path_funct {p} {A0 : @El0 p Type0}
  {x0 : El0 A0} {y0 : El0 A0} {q} (α : q ≤ p) :
  path A0 x0 y0 -> path (α · A0) (α · x0) (α · y0).
Proof.
intros [x].
(* definitional equations are of utmost importance here *)
exact (path_c (α · A0) (promote α · x)).
Defined.

Inductive pathR {p} (A0 : @El0 p Type0) :
 forall (x0 : El0 A0) (y0 : El0 A0)
 (p : forall q (α : q ≤ p), path (α · A0) (α · x0) (α · y0)), SProp :=
| pathr : forall (x : El0 (squish · A0)),
  pathR A0 (side_0 · x) (side_1 · x) (fun q α => path_c (α · A0) ((promote α) · x)).

Definition eq0 {p}
  (A0 : @El0 p Type0)
  (x0 : El0 A0)
  (y0 : El0 A0) :
  @El0 p Type0.
Proof.
unshelve refine (fun q α => mkYFT _ _ _ _).
- unshelve refine (fun r β => _).
  exact (path ((α ∘ β) · A0) ((α ∘ β) · x0) ((α ∘ β) · y0)).
- unshelve refine (fun r β s => _). simpl in s.
  exact (pathR ((α ∘ β) · A0) ((α ∘ β) · x0) ((α ∘ β) · y0) s).
- easy. (** TODO **)
Defined.

Definition eq1 {p}
  (A0 : @El0 p Type0)
  (x0 : El0 A0)
  (y0 : El0 A0) :
  @El1 p Type0 Type1 (eq0 A0 x0 y0).
Proof.
unshelve refine (fun q α r β => _). reflexivity.
Defined.

Definition refl0 {p}
  (A0 : @El0 p Type0)
  (x0 : El0 A0) :
  @El0 p (eq0 A0 x0 x0).
Proof.
unshelve refine (fun q α => _). simpl.
exact (path_c (α · A0) ((α ∘ squish) · x0)).
Defined.

Definition refl1 {p}
  (A0 : @El0 p Type0)
  (x0 : El0 A0) :
  @El1 p (eq0 A0 x0 x0) (eq1 A0 x0 x0) (refl0 A0 x0).
Proof.
unshelve refine (fun q α => _).
exact (pathr (α · A0) (α ∘ squish · x0)).
Defined.

(* The full transp0 will just be like □transp0_aux *)
Definition transp0_aux {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (x0 : El0 (app0 P0 a0 a1))
  (x1 : El1 _ (app1 P1 a0 a1) x0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 a0 b0))
  (e1 : El1 _ (eq1 A0 a0 b0) e0) :
  (app0 P0 b0 b1 p !).(yft0) p !.
Proof.
  unfold El0 in A0. simpl in A0.
  (* unfold El1 in A1. simpl in A1. unfold cast0 in A1. simpl in A1. *)
  unfold El0 in P0. simpl in P0.
  (* unfold El1 in P1. simpl in P1. unfold cast0 in P1. simpl in P1. *)
  unfold El0 in a0.
  unfold El0 in x0. unfold app0 in x0.
  unfold El0 in e0. simpl in e0.
  unfold app0.
  unshelve refine (
    match (e0 p !) with
    | path_c _ z0 => _
    end
  ).
  unfold El0 in z0.


(* etc etc *)
