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

(* Type of presheaves *)

Record Psh@{i} : Type :=
mkPsh {
  psh0 : forall p : ℙ, Type@{i};
  psh1 : forall p : ℙ, (forall q (α : q ≤ p), psh0 q) -> SProp;
}.

Definition precofib (p : ℙ) : Set.
Admitted.

Definition cofib (p : ℙ) := forall q (α : q ≤ p), precofib q.

Definition is1 {p} : cofib p -> SProp.
Admitted.

Definition is1_funct {p q} (α : q ≤ p) (c : cofib p) : 
  is1 c -> is1 (α ⋅ c).
Admitted.

Definition is1_match {p} {X : Type} (c : cofib p) 
  (b1 : is1 c -> X) 
  (b2 : (is1 c -> sFalse) -> X) : X.
Admitted.

Definition lid (p : ℙ) := p ≤ 1.

(* welcome to fibrancy HELL *)
Record FPsh@{i} : Type :=
mkFPsh {
  fpsh0 : forall p : ℙ, Type@{i} ;
  fpsh1 : forall p : ℙ, (forall q (α : q ≤ p), fpsh0 q) -> SProp ;
  fpshl0 : forall (p : ℙ) (c : cofib p) (l l' : lid p)
    (s0 : forall (q : ℙ) (α : q ≤ S p) (αε : is1 (squish ∘ α ⋅ c)), fpsh0 q)
    (s1 : forall (q : ℙ) (α : q ≤ S p) (αε : is1 (squish ∘ α ⋅ c)), fpsh1 q (fun r β => s0 r (α ∘ β) (is1_funct β _ αε)))
    (l0 : forall (q : ℙ) (α : q ≤ p), fpsh0 q)
    (l1 : forall (q : ℙ) (α : q ≤ p), 
      fpsh1 q (fun r β => is1_match (α ∘ β ⋅ c)
        (fun βε => s0 r ((merge ! l) ∘ α ∘ β) βε)
        (fun _ => l0 r (α ∘ β)))),
    fpsh0 p ;
  fpshl1 : forall (p : ℙ) (c : cofib p) (l l' : lid p)
    (s0 : forall (q : ℙ) (α : q ≤ S p) (αε : is1 (squish ∘ α ⋅ c)), fpsh0 q)
    (s1 : forall (q : ℙ) (α : q ≤ S p) (αε : is1 (squish ∘ α ⋅ c)), fpsh1 q (fun r β => s0 r (α ∘ β) (is1_funct β _ αε)))
    (l0 : forall (q : ℙ) (α : q ≤ p), fpsh0 q)
    (l1 : forall (q : ℙ) (α : q ≤ p), 
      fpsh1 q (fun r β => is1_match (α ∘ β ⋅ c)
        (fun βε => s0 r ((merge ! l) ∘ α ∘ β) βε)
        (fun _ => l0 r (α ∘ β)))),
    fpsh1 p (fun q α => is1_match (α ⋅ c)
      (fun αε => s0 q ((merge ! l') ∘ α) αε)
      (fun _ => fpshl0 q (α ⋅ c) (l ∘ α) (l' ∘ α)
        (fun r β βε => s0 r (promote α ∘ β) βε)
        (fun r β βε => s1 r (promote α ∘ β) βε)
        (α ⋅ l0) (α ⋅ l1))) ;
}.

(* Elements of a presheaf *)

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

(* Type of presheaves over yoneda(p) *)

Record yt@{i} (p : ℙ) := mkYT {
  yt0 : forall q (α : q ≤ p), Type@{i};
  yt1 : forall q (α : q ≤ p), (forall r (β : r ≤ q), yt0 r (α ∘ β)) -> SProp;
}.

Arguments yt0 {_}.
Arguments yt1 {_}.

Definition yt_funct@{i} {p q} (α : q ≤ p) (f : yt@{i} p) : yt@{i} q :=
mkYT@{i} q (α ⋅ f.(yt0)) (α ⋅ f.(yt1)).

(* Sections of a presheaf over yoneda(p) *)

Record ytEl@{i j} {p : ℙ} (f : yt@{i} p) : Type@{j} :=
mkYtEl {
  ytel0 : forall q (α : q ≤ p), f.(yt0) q α;
  ytel1 : forall q (α : q ≤ p), f.(yt1) q α (α · ytel0);
}.

Arguments ytel0 {_ _}.
Arguments ytel1 {_ _}.

Definition exteq_ytEl {p : ℙ} {f : yt p} (s t : ytEl f) :=
  forall q α, s.(ytel0) q α ≡ s.(ytel0) q α.

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

Record yft@{i j} (p : ℙ) := mkYFT {
  yft0 : forall q (α : q ≤ p), Type@{i};
  yft1 : forall q (α : q ≤ p), (forall r (β : r ≤ q), yft0 r (α ∘ β)) -> SProp;
  yftl0 : forall (q : ℙ) (α : S q ≤ p) (c : cofib q) (l l' : lid q)
    (s0 : forall (r : ℙ) (β : r ≤ S q) (βε : is1 (squish ∘ β ⋅ c)), yft0 r (α ∘ β))
    (s1 : forall (r : ℙ) (β : r ≤ S q) (βε : is1 (squish ∘ β ⋅ c)), yft1 r (α ∘ β) (fun r0 β0 => s0 r0 (β ∘ β0) (is1_funct β0 _ βε)))
    (l0 : forall (r : ℙ) (β : r ≤ q), yft0 r (α ∘ (merge ! l) ∘ β))
    (l1 : forall (r : ℙ) (β : r ≤ q), 
      yft1 r (α ∘ (merge ! l) ∘ β) (fun r0 β0 => is1_match (β ∘ β0 ⋅ c)
        (fun β0ε => s0 r0 ((merge ! l) ∘ β ∘ β0) β0ε)
        (fun _ => l0 r0 (β ∘ β0)))),
    yft0 q (α ∘ (merge ! l')) ;
  yftl1 : forall (q : ℙ) (α : S q ≤ p) (c : cofib q) (l l' : lid q)
    (s0 : forall (r : ℙ) (β : r ≤ S q) (βε : is1 (squish ∘ β ⋅ c)), yft0 r (α ∘ β))
    (s1 : forall (r : ℙ) (β : r ≤ S q) (βε : is1 (squish ∘ β ⋅ c)), yft1 r (α ∘ β) (fun r0 β0 => s0 r0 (β ∘ β0) (is1_funct β0 _ βε)))
    (l0 : forall (r : ℙ) (β : r ≤ q), yft0 r (α ∘ (merge ! l) ∘ β))
    (l1 : forall (r : ℙ) (β : r ≤ q), 
      yft1 r (α ∘ (merge ! l) ∘ β) (fun r0 β0 => is1_match (β ∘ β0 ⋅ c)
        (fun β0ε => s0 r0 ((merge ! l) ∘ β ∘ β0) β0ε)
        (fun _ => l0 r0 (β ∘ β0)))),
    yft1 q (α ∘ (merge ! l')) (fun r β => is1_match (β ⋅ c)
      (fun βε => s0 r ((merge ! l') ∘ β) βε)
      (fun _ => yftl0 r (α ∘ promote β) (β ⋅ c) (l ∘ β) (l' ∘ β)
        (fun r0 β0 β0ε => s0 r0 (promote β ∘ β0) β0ε)
        (fun r0 β0 β0ε => s1 r0 (promote β ∘ β0) β0ε)
        (β ⋅ l0) (β ⋅ l1))) ;
}.

Arguments yft0 {_}.
Arguments yft1 {_}.
Arguments yftl0 {_}.
Arguments yftl1 {_}.

Definition yft_funct@{i j} {p q : ℙ} (α : q ≤ p) :
  yft@{i j} p -> yft@{i j} q :=
fun f =>
{|
  yft0 := α · yft0 f;
  yft1 := α ⋅ yft1 f;
  yftl0 := α ⋅ yftl0 f;
  yftl1 := α ⋅ yftl1 f;
|}.

Definition yftR@{i j k} {p : ℙ} (s : forall q : nat, q ≤ p -> yft@{i j} q) : SProp :=
  forall q α, seq@{k} (s q α) (yft_funct α (s p !)).

Definition cast0 {p : ℙ}
  (A0 : forall q (α : q ≤ p), yft q)
  (A1 : forall q (α : q ≤ p), yftR (α · A0))
  {q} (α : q ≤ p) {r} (β : r ≤ q) :
  (A0 r (α ∘ β)).(yft0) r ! -> (A0 q α).(yft0) r β.
Proof.
refine (fun x => _).
refine (J_seq _ _ (fun X _ => yft0 X r !) x _ (A1 q α r β)).
Defined.

(* Sections of fibrant presheaves over yoneda(p) *)

Record yftEl@{i j k} {p : ℙ} (f : yft@{i j} p) : Type@{k} :=
mkYftEl {
  yftel0 : forall q (α : q ≤ p), f.(yft0) q α;
  yftel1 : forall q (α : q ≤ p), f.(yft1) q α (α · yftel0);
}.

Arguments yftel0 {_ _}.
Arguments yftel1 {_ _}.

Definition seq_yftEl {p : ℙ} {f : yft p} {s t : yftEl f} :
  yftel0 s ≡ yftel0 t -> s ≡ t.
Proof.
  intro H.
  unshelve refine (J_seqs _ (yftel0 s)
    (fun t0 e0 => s ≡ {| yftel0 := t0 ; yftel1 := J_seqs _ (yftel0 s) (fun u0 _ => forall q (α : q ≤ p), f.(yft1) q α (α ⋅ u0)) (yftel1 s) t0 e0 |})
    (srefl _) (yftel0 t) H).
Defined.

Definition yftEl_funct@{i j k} {p q} {f : yft@{i j} p} (α : q ≤ p) :
  yftEl@{i j k} f -> yftEl@{i j k} (yft_funct@{i j} α f) :=
fun s => mkYftEl@{i j k} q (yft_funct α f) (α ⋅ s.(yftel0)) (α ⋅ s.(yftel1)).


(* Universe of fibrant types *)

Definition Uᶠ@{i j k l} : Psh@{l} :=
mkPsh@{l} yft@{i j} (fun p s => yftR@{i j k} s).

Definition Glue {p : ℙ} 
  (c : cofib p) (l l' : lid p)
  (s0 : forall q (α : q ≤ S p), is1 (squish ∘ α ⋅ c) -> yft q)
  (s1 : forall q (α : q ≤ S p) (αε : is1 (squish ∘ α ⋅ c)),
    yftR (fun r β => s0 r (α ∘ β) (is1_funct β _ αε)))
  (l0 : forall q (α : q ≤ p), yft q)
  (l1 : forall q (α : q ≤ p), yftR (fun r β => is1_match (α ∘ β ⋅ c)
    (fun βε => s0 r (merge ! l ∘ α ∘ β) βε)
    (fun _ => l0 r (α ∘ β)))) :
  yft p.
Proof.
Admitted.

Definition U0 (p : ℙ) : psh0 Uᶠ p.
Proof.
unshelve econstructor.
- exact (fun q α => yft q).
- refine (fun q α s => yftR s).
- refine (fun q α c l l' s0 s1 l0 l1 => _).
  refine (Glue c l l' s0 s1 l0 l1).
- refine (fun q α c l l' s0 s1 l0 l1 => _).
  apply sfalso.
Defined.

Definition U1 (p : ℙ) : psh1 Uᶠ p (fun q α => U0 q).
Proof.
refine (fun q α => _).
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

Definition boolR {p} : (forall q (α : q ≤ p), bool) -> SProp :=
fun s => s ≡ fun q α => s p !.

Definition bool0 {p} : @El0 p Type0.
Proof.
unshelve econstructor.
- refine (fun r β => bool).
- refine (fun r β s => boolR s).
- refine (fun r β c l l' s0 s1 l0 l1 => _). apply falso.
- refine (fun r β c l l' s0 s1 l0 l1 => _). apply sfalso.
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
reflexivity.
Defined.

(* Translation of Arrow types *)

Definition Arr0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0) :
  @El0 p Type0.
Proof.
unshelve econstructor.
- unshelve refine (fun r β =>
  forall
  (x0 : El0 (α ∘ β · A0))
  (x1 : El1 (α ∘ β · A0) (α ∘ β · A1) x0)
  ,
  (B0 r (α ∘ β)).(yft0) r !).
- unshelve refine (fun r β f =>
  forall
  (x0 : El0 (α ∘ β · A0))
  (x1 : El1 (α ∘ β · A0) (α ∘ β · A1) x0)
  ,
  (B0 r (α ∘ β)).(yft1) r ! (fun r' β' => _)).
  unshelve refine (cast0 B0 B1 (α ∘ β) β' _).
  exact (f r' β' (β' · x0) (β' · x1)).
- refine (fun r β c l l' s0 s1 l0 l1 x0 x1 => _).
  simpl in *. apply falso.
- refine (fun r β c l l' s0 s1 l0 l1 x0 x1 => _). apply sfalso.
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

(* Translation of sigmas *)

Inductive SigmaT {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0) :
  Type :=
| Sigma_c : forall (a0 : El0 A0) (a1 : El1 A0 A1 a0)
  (b0 : El0 (app0 P0 a0 a1)) (b1 : El1 _ (app1 P1 a0 a1) b0),
  SigmaT A0 A1 P0 P1.

Definition SigmaT_funct {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  {q} (α : q ≤ p) :
  SigmaT A0 A1 P0 P1 -> SigmaT (α ⋅ A0) (α ⋅ A1) (α ⋅ P0) (α ⋅ P1).
Proof.
intros [a0 a1 b0 b1].
exact (Sigma_c _ _ _ _ (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1)).
Defined.

Definition SigmaR {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0)
  : (forall q (α : q ≤ p), SigmaT (α ⋅ A0) (α ⋅ A1) (α ⋅ P0) (α ⋅ P1)) -> SProp :=
fun s => s ≡ fun q α => SigmaT_funct α (s p !).

Definition Sigma0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0) :
  @El0 p Type0.
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β => _).
  exact (SigmaT (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (α ∘ β ⋅ P0) (α ∘ β ⋅ P1)).
- refine (fun r β => _).
  exact (SigmaR (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (α ∘ β ⋅ P0) (α ∘ β ⋅ P1)).
- refine (fun r β c l l' s0 s1 l0 l1 => _). apply falso.
- refine (fun r β c l l' s0 s1 l0 l1 => _). apply sfalso.
Defined.

Definition Sigma1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0) :
  @El1 p Type0 Type1 (Sigma0 A0 A1 P0 P1).
Proof.
refine (fun q α r β => _).
reflexivity.
Defined.

Definition fst0 {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (x0 : El0 (Sigma0 A0 A1 P0 P1)) :
  El0 A0.
Proof.
destruct (x0 p !) as [a0 a1 b0 b1].
exact a0.
Defined.

Definition fst1 {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (x0 : El0 (Sigma0 A0 A1 P0 P1)) :
  El1 A0 A1 (fst0 x0).
Proof.
unfold fst0.
destruct (x0 p !) as [a0 a1 b0 b1].
exact a1.
Defined.

Definition snd0 {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (x0 : El0 (Sigma0 A0 A1 P0 P1)) :
  El0 (app0 P0 (fst0 x0) (fst1 x0)).
Proof.
unfold fst0. unfold fst1.
destruct (x0 p !) as [a0 a1 b0 b1].
exact b0.
Defined.

Definition snd1 {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (x0 : El0 (Sigma0 A0 A1 P0 P1)) :
  El1 _ (app1 P1 (fst0 x0) (fst1 x0)) (snd0 x0).
Proof.
unfold fst0. unfold fst1. unfold snd0.
destruct (x0 p !) as [a0 a1 b0 b1].
exact b1.
Defined.

Definition seq_Sigma_transp {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  {a0 : El0 (Sigma0 A0 A1 P0 P1)}
  {b0 : El0 (Sigma0 A0 A1 P0 P1)}
  : fst0 a0 ≡ fst0 b0 ->
    El0 (app0 P0 (fst0 a0) (fst1 a0)) ->
    El0 (app0 P0 (fst0 b0) (fst1 b0)).
Proof.
refine (fun H x => _).
refine (J_seq _ (fst0 a0)
  (fun x e => El0 (app0 P0 x
    (J_seqs _ (fst0 a0) (fun y _ => El1 A0 A1 y) (fst1 a0) x e)))
  x (fst0 b0) H).
Defined.

Definition seq_Sigma {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (a0 : El0 (Sigma0 A0 A1 P0 P1))
  (a1 : El1 _ (Sigma1 A0 A1 P0 P1) a0)
  (b0 : El0 (Sigma0 A0 A1 P0 P1))
  (b1 : El1 _ (Sigma1 A0 A1 P0 P1) b0)
  : forall (e0 : fst0 a0 ≡ fst0 b0)
    (e1 : seq_Sigma_transp e0 (snd0 a0) ≡ snd0 b0),
    a0 ≡ b0.
Proof.
refine (fun H0 H1 => _).
refine (J_seqs _ _ (fun x _ => x ≡ b0) _ a0 (ssym (a1 p !))).
unfold cast0 ; simpl.
assert (a0 p ! ≡ b0 p !).
admit.
refine (J_seqs _ _ (fun x _ => (fun q α => SigmaT_funct α x) ≡ b0) _ _ (ssym H)).
exact (ssym (b1 p !)).
Admitted.

(* Inductive SigmaT {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0) :
  Type :=
| Sigma_c : forall (a0 : El0 A0) (a1 : El1 A0 A1 a0)
  (b0 : El0 (app0 P0 a0 a1)) (b1 : El1 _ (app1 P1 a0 a1) b0),
  SigmaT A0 A1 P0 P1.
Definition SigmaT_funct {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  {q} (α : q ≤ p) :
  SigmaT A0 A1 P0 P1 -> SigmaT (α ⋅ A0) (α ⋅ A1) (α ⋅ P0) (α ⋅ P1).
Proof.
intros [a0 a1 b0 b1].
exact (Sigma_c _ _ _ _ (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1)).
Defined.
Definition fst0_SigmaT {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (x0 : SigmaT A0 A1 P0 P1) :
  El0 A0.
Proof.
destruct x0 as [a0 a1 b0 b1].
exact a0.
Defined.
Definition fst1_SigmaT {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (x0 : SigmaT A0 A1 P0 P1) :
  El1 A0 A1 (fst0_SigmaT x0).
Proof.
destruct x0 as [a0 a1 b0 b1].
exact a1.
Defined.
Definition snd_SigmaT {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (x0 : SigmaT A0 A1 P0 P1) :
  El0 (app0 P0 (fst0_SigmaT x0) (fst1_SigmaT x0)).
Proof.
unfold fst0_SigmaT. unfold fst1_SigmaT.
destruct x0 as [a0 a1 b0 b1].
exact b0.
Defined.
Definition seq_SigmaT_transp {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  {a0 : SigmaT A0 A1 P0 P1}
  {b0 : SigmaT A0 A1 P0 P1}
  : fst0_SigmaT a0 ≡ fst0_SigmaT b0 ->
    El0 (app0 P0 (fst0_SigmaT a0) (fst1_SigmaT a0)) ->
    El0 (app0 P0 (fst0_SigmaT b0) (fst1_SigmaT b0)).
Proof.
refine (fun H x => _).
refine (J_seq _ (fst0_SigmaT a0)
  (fun x e => El0 (app0 P0 x
    (J_seqs _ (fst0_SigmaT a0) (fun y _ => El1 A0 A1 y) (fst1_SigmaT a0) x e)))
  x (fst0_SigmaT b0) H).
Defined.
Definition seq_SigmaT {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (a0 : SigmaT A0 A1 P0 P1)
  (b0 : SigmaT A0 A1 P0 P1)
  : forall (e0 : fst0_SigmaT a0 ≡ fst0_SigmaT b0)
    (e1 : seq_SigmaT_transp e0 (snd_SigmaT a0) ≡ snd_SigmaT b0),
    a0 ≡ b0.
Proof.
refine (fun H0 H1 => _).
unfold seq_SigmaT_transp in H1.
unfold snd_SigmaT in H1.
unfold fst1_SigmaT in H1.
unfold fst0_SigmaT in H1.
unfold fst0_SigmaT in H0.
destruct a0.
destruct b0.
destruct H0.
simpl in H1.
destruct H1.
reflexivity.
Defined.
Definition SigmaR {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0)
  : (forall q (α : q ≤ p), SigmaT (α ⋅ A0) (α ⋅ A1) (α ⋅ P0) (α ⋅ P1)) -> SProp :=
fun s => s ≡ fun q α => SigmaT_funct α (s p !).
Definition Sigma0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0) :
  @El0 p Type0.
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β => _).
  exact (SigmaT (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (α ∘ β ⋅ P0) (α ∘ β ⋅ P1)).
- refine (fun r β => _).
  exact (SigmaR (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (α ∘ β ⋅ P0) (α ∘ β ⋅ P1)).
- refine (fun r β b e l le l' => _).
  apply falso.
Defined.
Definition Sigma1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0) :
  @El1 p Type0 Type1 (Sigma0 A0 A1 P0 P1).
Proof.
refine (fun q α => _).
reflexivity.
Defined. *)

Definition dpair0 {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 (app0 P0 a0 a1))
  (b1 : El1 _ (app1 P1 a0 a1) b0)
  : El0 (Sigma0 A0 A1 P0 P1).
Proof.
refine (fun q α => _) ; simpl.
exact (Sigma_c _ _ _ _ (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1)).
Defined.

Definition dpair1 {p}
  {A0 : @El0 p Type0}
  {A1 : @El1 p Type0 Type1 A0}
  {P0 : El0 (Arr0 A0 A1 Type0 Type1)}
  {P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0}
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 (app0 P0 a0 a1))
  (b1 : El1 _ (app1 P1 a0 a1) b0)
  : El1 _ (Sigma1 A0 A1 P0 P1) (dpair0 a0 a1 b0 b1).
Proof.
refine (fun q α => _) ; simpl.
reflexivity.
Defined.

(* Dependent products *)

Definition Prod0 {p}
  (A0 : @El0 p Type0)
  (A1 : El1 Type0 Type1 A0)
  (B0 : @El0 p (Arr0 A0 A1 Type0 Type1))
  (B1 : El1 (Arr0 A0 A1 Type0 Type1) (Arr1 A0 A1 Type0 Type1) B0)
  : @El0 p Type0.
Proof.
unshelve econstructor.
- unshelve refine (fun r β =>
  forall
  (x0 : El0 (α ∘ β · A0))
  (x1 : El1 (α ∘ β · A0) (α ∘ β · A1) x0)
  ,
  (B0 r (α ∘ β) x0 x1).(yft0) r !).
- unshelve refine (fun r β f0 =>
  forall
  (x0 : El0 (α ∘ β · A0))
  (x1 : El1 (α ∘ β · A0) (α ∘ β · A1) x0)
  ,
  (B0 r (α ∘ β) x0 x1).(yft1) r ! (fun r2 β2 => _)).
  unshelve refine (@cast0 r
    (fun r3 (β3 : r3 ≤ r) => B0 r3 (α ∘ β ∘ β3) (β3 · x0) (β3 · x1))
    (fun r3 (β3 : r3 ≤ r) => B1 r3 (α ∘ β ∘ β3) (β3 · x0) (β3 · x1))
    _ ! _ β2 (f0 r2 _ (β2 · x0) (β2 · x1))).
- refine (fun r β c l l' s0 s1 l0 l1 x0 x1 => _). apply falso.
- refine (fun r β c l l' s0 s1 l0 l1 x0 x1 => _). apply sfalso.
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


(* cubical equality *)

Record cube_eq {p} (A0 : @El0 p Type0) (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0) (y0 : El0 A0) : Type :=
mkCE {
  ce_f0 : El0 (squish ⋅ A0) ;
  ce_f1 : El1 (squish ⋅ A0) (squish ⋅ A1) ce_f0 ;
  ce_s : side_0 ⋅ ce_f0 ≡ x0 ;
  ce_t : side_1 ⋅ ce_f0 ≡ y0 ;
}.

Arguments ce_f0 {_ _ _ _ _}.
Arguments ce_f1 {_ _ _ _ _}.
Arguments ce_s {_ _ _ _ _}.
Arguments ce_t {_ _ _ _ _}.

Definition ce_funct {p} {A0 : @El0 p Type0} {A1 : @El1 p Type0 Type1 A0}
  {x0 : El0 A0} {y0 : El0 A0} {q} (α : q ≤ p) :
  cube_eq A0 A1 x0 y0 -> cube_eq (α · A0) (α ⋅ A1) (α · x0) (α · y0).
Proof.
unshelve refine (fun x => _).
unshelve econstructor.
- exact (promote α ⋅ x.(ce_f0)).
- exact (promote α ⋅ x.(ce_f1)).
- refine (J_seqs _ _ (fun u _ => _ ≡ α ⋅ u) (srefl _) x0 (x.(ce_s))).
- refine (J_seqs _ _ (fun u _ => _ ≡ α ⋅ u) (srefl _) y0 (x.(ce_t))).
Defined.

Definition cube_eqR {p} (A0 : @El0 p Type0) (A1 : @El1 p Type0 Type1 A0)
 (x0 : El0 A0) (y0 : El0 A0) :
 (forall q (α : q ≤ p), cube_eq (α · A0) (α ⋅ A1) (α · x0) (α · y0)) -> SProp :=
fun s => s ≡ fun q α => ce_funct α (s p !).

Definition eq0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
  (y0 : El0 A0)
  (y1 : El1 A0 A1 y0) :
  @El0 p Type0.
Proof.
unshelve econstructor.
- unshelve refine (fun r β => _).
  exact (cube_eq ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · x0) ((α ∘ β) · y0)).
- unshelve refine (fun r β s => _). simpl in s.
  exact (cube_eqR ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · x0) ((α ∘ β) · y0) s).
- refine (fun r β c l l' s0 s1 l0 l1 => _). apply falso.
- refine (fun r β c l l' s0 s1 l0 l1 => _). apply sfalso.
Defined.

Definition eq1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
  (y0 : El0 A0)
  (y1 : El1 A0 A1 y0) :
  @El1 p Type0 Type1 (eq0 A0 A1 x0 x1 y0 y1).
Proof.
unshelve refine (fun q α r β => _). reflexivity.
Defined.

Definition eq_refl0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0) :
  @El0 p (eq0 A0 A1 x0 x1 x0 x1).
Proof.
unshelve refine (fun q α => _). simpl.
unshelve econstructor.
- exact ((α ∘ squish) ⋅ x0).
- exact ((α ∘ squish) ⋅ x1).
- reflexivity.
- reflexivity.
Defined.

Definition eq_refl1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0) :
  @El1 p (eq0 A0 A1 x0 x1 x0 x1) (eq1 A0 A1 x0 x1 x0 x1) (eq_refl0 A0 A1 x0 x1).
Proof.
unshelve refine (fun q α => _).
reflexivity.
Defined.
