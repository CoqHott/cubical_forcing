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

(* generating cofibrations, AFH style *)
(* question : do we want to make it into a presheaf to
   get functoriality ?  *)

Definition cofib (p : ℙ) : Set.
Admitted.

Definition cofib_funct {p q : ℙ} (α : q ≤ p) :
  cofib p -> cofib q.
Admitted.

Definition cofibface {p q : ℙ} (b : cofib p) (α : q ≤ p) : bool.
Admitted.

Definition tubeface {p q : ℙ} (b : cofib p) (α : q ≤ S p) : bool.
Admitted.

(* sections of yoneda(S p) -> yoneda(p) *)

Definition lid (p : ℙ) : Set.
Admitted.

Definition lidface {p : ℙ} (l : lid p) : p ≤ S p.
Admitted.

(* Partial sections of a presheaf over yoneda(p) *)

Record partialEl@{i j} {p : ℙ} (t : yt@{i} p)
  (domain : forall q (α : q ≤ p), bool) :=
mkPartialEl {
  pe_el : forall q (α : q ≤ p) (Hα : domain q α ≡ true),
    ytEl@{i j} (yt_funct@{i} α t) ;
  pe_compat : forall q (α : q ≤ p) (Hα : domain q α ≡ true)
    r (β : r ≤ q) (Hβ : domain r (α ∘ β) ≡ true),
    ytEl_funct β (pe_el q α Hα) ≡ pe_el r (α ∘ β) Hβ ;
}.

Arguments pe_el {_ _ _}.
Arguments pe_compat {_ _ _}.

Definition tubeEl@{i j} {p : ℙ} (t : yt@{i} (S p))
  (b : cofib p)
 := partialEl t (fun q α => tubeface b α).

Record lidEl@{i j} {p : ℙ} {t : yt@{i} (S p)}
  {b : cofib p} (e : tubeEl@{i j} t b) (l : lid p) :=
mkLidEl {
  le_el : ytEl@{i j} (yt_funct@{i} (lidface l) t) ;
  le_compat : forall q (α : q ≤ p)
    (Hα : tubeface b ((lidface l) ∘ α) ≡ true),
    ytEl_funct α le_el ≡ e.(pe_el) q ((lidface l) ∘ α) Hα ;
}.

(* With this, we can define a fibration structure *)
(* A presheaf over yoneda(p) is fibrant if all partial sections
   have fillers *)

Definition fibstruct@{i j} (p : ℙ)
  (t0 : forall q (α : q ≤ S p), Type@{i})
  (t1 : forall q (α : q ≤ S p) (s : forall r (β : r ≤ q), t0 r (α ∘ β)), SProp)
  : Type@{i} :=
forall (b : cofib p) (e : tubeEl@{i j} (mkYT (S p) t0 t1) b)
  (l : lid p) (le : lidEl@{i j} e l) (l' : lid p),
  lidEl@{i j} e l'.

(* Type of fibrant presheaves over yoneda(p) *)

Record yft@{i j} (p : ℙ) := mkYFT {
  yft0 : forall q (α : q ≤ p), Type@{i};
  yft1 : forall q (α : q ≤ p), (forall r (β : r ≤ q), yft0 r (α ∘ β)) -> SProp;
  yftfib : forall q (α : S q ≤ p), fibstruct@{i j} q (α ⋅ yft0) (α ⋅ yft1);
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
  yftfib := α ⋅ yftfib f;
|}.

(* original version had an extensional version of this *)
Definition yftR@{i j k} {p : ℙ} (s : forall q : nat, q ≤ p -> yft@{i j} q) : SProp :=
  seq@{k} s (fun q α => yft_funct@{i j} α (s p !)).

Definition cast0 {p : ℙ}
  (A0 : forall q (α : q ≤ p), yft q)
  (A1 : forall q (α : q ≤ p), yftR (α · A0))
  {q} (α : q ≤ p) {r} (β : r ≤ q) :
  (A0 r (α ∘ β)).(yft0) r ! -> (A0 q α).(yft0) r β.
Proof.
refine (fun x => _).
refine (J_seq _ (α ⋅ A0) (fun a _ => (a r β).(yft0) r !) x _ (A1 q α)).
Defined.

Definition seq_yftAlt {p : ℙ}
  {t1 t2 : ytEl {| yt0 := fun q (_ : q ≤ p) => yft q ;
                   yt1 := fun q (_ : q ≤ p) s => yftR s ; |}} :
  t1.(ytel0) p ! ≡ t2.(ytel0) p ! -> t1 ≡ t2.
Proof.
intro H. apply seq_ytEl.
pose proof (ytel1 t1 p !) as H1 ; simpl in H1.
refine (J_seqs _ _
  (fun x _ => x ≡ ytel0 t2) _ (ytel0 t1) (ssym H1)).
refine (J_seqs _ (ytel0 t2 p !)
  (fun x _ => (fun q α => yft_funct α x) ≡ ytel0 t2)
  _ (ytel0 t1 p !) (ssym H)).
pose proof (ytel1 t2 p !) as H2 ; simpl in H2.
refine (J_seqs _ _
  (fun x _ => (fun q α => yft_funct α (ytel0 t2 p !)) ≡ x)
  (srefl _) (ytel0 t2) (ssym H2)).
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

(* Partial fibrant presheaves over yoneda(S p) *)

Definition partialYft@{i j k l} {p : ℙ}
  (domain : forall q (α : q ≤ p), bool) :=
  partialEl@{k l}
    {| yt0 := fun q (_ : q ≤ p) => yft@{i j} q ;
       yt1 := fun q (_ : q ≤ p) s => yftR s ; |} domain.

Definition tubeYft@{i j k l} {p : ℙ} (b : cofib p) :=
  tubeEl@{k l}
    {| yt0 := fun q (_ : q ≤ S p) => yft@{i j} q ;
       yt1 := fun q (_ : q ≤ S p) s => yftR s ; |} b.

Definition lidYft@{i j k l} {p : ℙ} {b : cofib p}
  (t : tubeYft@{i j k l} b) (l : lid p) :=
  lidEl@{k l} t l.

(* Sections of a partial fibrant presheaf over yoneda(S p) *)
(* this definition is function-based, and therefore not very
   extensional. It is quite possible we will need to make it
   list-based so that partial types satisfy some extensionality *)

(* Definition boxYftEq {p : ℙ} {b : box p} (t : boxYft b)
  {q : ℙ} (α : q ≤ S p) (Hα : boxface b α ≡ true)
  {r : ℙ} (β : r ≤ q) (Hβ : boxface b (α ∘ β) ≡ true) :
  ytel0 (be_el t r (α ∘ β) Hβ) r ! ≡ yft_funct β (ytel0 (be_el t q α Hα) q !).
Proof.
unshelve refine (J_seqs _ (ytEl_funct β (be_el t q α Hα))
  (fun x _ => ytel0 x r ! ≡ yft_funct β (ytel0 (be_el t q α Hα) q !))
  _ (be_el t r (α ∘ β) Hβ) (be_compat t _ α Hα _ β Hβ)).
exact (ytel1 (be_el t q α Hα) q ! r β).
Defined.

Record boxYftEl {p : ℙ} {b : box p} (t : boxYft b) : Type :=
mkBoxYftEl {
  bye0 : forall q (α : q ≤ S p) (Hα : boxface b α ≡ true),
    yftEl (ytel0 (t.(be_el) q α Hα) q !) ;
  bye1 : forall q (α : q ≤ S p) (Hα : boxface b α ≡ true)
    r (β : r ≤ q) (Hβ : boxface b (α ∘ β) ≡ true),
    yftEl_funct β (bye0 q α Hα) ≡ transp_seq yftEl (bye0 r (α ∘ β) Hβ) (boxYftEq t α Hα β Hβ) ;
}.

Definition boxYftEl' {p : ℙ} {b : box p} (t : boxYft b) : Type.
Proof.
  unshelve refine ((match (boxface b !) as bl return (boxface b ! ≡ bl) -> Type with
    | true => (fun Hα => _)
    | false => (fun _ => _)
    end) (srefl _)).
  - exact (yftEl (ytel0 (t.(be_el) _ ! Hα) (S p) !)).
  - exact (boxYftEl t).
Defined. *)

(* *)

Definition tubeGlue@{i j k l} {p : ℙ}
  {b : cofib p} (t : tubeYft@{i j k l} b)
  {l : lid p} (lt : lidYft@{i j k l} t l)
  (l' : lid p) {q} (α : q ≤ p) : Type@{i}.
Proof.
Admitted.

Definition tubeGlue_funct@{i j k l} {p : ℙ}
  {b : cofib p} {t : tubeYft@{i j k l} b}
  {l : lid p} {lt : lidYft@{i j k l} t l}
  {l' : lid p} {q} {α : q ≤ p}
  {r} (β : r ≤ q) :
  tubeGlue@{i j k l} t lt l' α -> tubeGlue@{i j k l} t lt l' (α ∘ β).
Proof.
Admitted.

Definition tubeGlueR@{i j k l} {p : ℙ}
  {b : cofib p} (t : tubeYft@{i j k l} b)
  {l : lid p} (lt : lidYft@{i j k l} t l)
  (l' : lid p) {q} (α : q ≤ p) :
  (forall r (β : r ≤ q), tubeGlue t lt l' (α ∘ β)) -> SProp.
Proof.
refine (fun s => _).
exact (forall r (β : r ≤ q), s r β ≡ tubeGlue_funct β (s q !)).
Defined.

Definition tubeGlueFib@{i j k l} {p : ℙ}
  {b : cofib p} (t : tubeYft@{i j k l} b)
  {l : lid p} (lt : lidYft@{i j k l} t l)
  (l' : lid p) {q} (α : S q ≤ p) :
  fibstruct q (fun _ β => tubeGlue t lt l' (α ∘ β))
    (fun _ β => tubeGlueR t lt l' (α ∘ β)).
Proof.
Admitted.

Definition tubeGlueLid@{i j k l} {p : ℙ}
  {b : cofib p} (t : tubeYft@{i j k l} b)
  {l : lid p} (lt : lidYft@{i j k l} t l)
  (l' : lid p) :
  lidYft@{i j k l} t l'.
Proof.
unshelve econstructor.
- unfold yt_funct ; simpl. unshelve econstructor ; simpl.
  + refine (fun q α => _).
    unshelve econstructor.
    * admit. (* refine (fun r β => tubeGlue@{i j k l} t lt l' (α ∘ β)). *)
    * admit. (*  refine (fun r β => tubeGlueR@{i j k l} t lt l' (α ∘ β)). *)
    * admit. (* refine (fun r β => tubeGlueFib t lt l' (α ∘ β)). *)
  + refine (fun q α => _).
    unfold yftR. unfold yft_funct ; simpl. admit. (* reflexivity. *)
- unshelve refine (fun q α Hα => _).
  unfold ytEl_funct ; simpl.
  apply seq_yftAlt ; simpl.
  (** FUNEXT PROBLEM **)
Admitted.

(* Universe of fibrant types *)

Definition Uᶠ@{i j k l} : Psh@{l} :=
mkPsh@{l} yft@{i j} (fun p s => yftR@{i j k} s).

Definition U0 (p : ℙ) : psh0 Uᶠ p.
Proof.
unshelve econstructor.
- exact (fun q α => yft q).
- refine (fun q α s => yftR s).
- refine (fun q α b e l le l' => _).
  change (tubeYft b) in e. change (lidYft e l) in le. change (lidYft e l').
  refine (tubeGlueLid e le l').
Defined.

Definition U1 (p : ℙ) : psh1 Uᶠ p (fun q α => U0 q).
Proof.
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
unshelve refine (fun q α => mkYFT _ _ _ _).
- unshelve refine (fun r β => bool).
- unshelve refine (fun r β s => boolR s).
- unshelve refine (fun r β b e l le l' => _).
  unshelve econstructor.
  + unfold yt_funct ; simpl.
    unshelve econstructor ; simpl.
    apply falso.
    apply sfalso.
  + apply sfalso.
Defined.

Definition bool1 {p} : @El1 p Type0 Type1 bool0.
Proof.
unshelve refine (fun q α => _).
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
unshelve refine (fun q α => mkYFT _ _ _ _).
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
- unshelve refine (fun r β b e l le l' => _).
  unshelve econstructor.
  + unfold yt_funct ; simpl.
    unshelve econstructor ; simpl.
    * refine (fun r0 β0 x0 x1 => _).
      apply falso.
    * refine (fun r0 β0 x0 x1 => _).
      apply sfalso.
  + refine (fun r0 β0 Hβ0 => _).
    unfold ytEl_funct ; simpl.
    apply seq_ytEl ; simpl.
    apply sfalso.
Defined.

Definition Arr1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0) :
  @El1 p Type0 Type1 (Arr0 A0 A1 B0 B1).
Proof.
unshelve refine (fun q α => _).
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

(* Translation of equality *)

Record path {p} (A0 : @El0 p Type0) (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0) (y0 : El0 A0) : Type :=
mkPath {
  path_f0 : El0 (squish ⋅ A0) ;
  path_f1 : El1 (squish ⋅ A0) (squish ⋅ A1) path_f0 ;
  path_s : side_0 ⋅ path_f0 ≡ x0 ;
  path_t : side_1 ⋅ path_f0 ≡ y0 ;
}.

Arguments path_f0 {_ _ _ _ _}.
Arguments path_f1 {_ _ _ _ _}.
Arguments path_s {_ _ _ _ _}.
Arguments path_t {_ _ _ _ _}.

Definition path_funct {p} {A0 : @El0 p Type0} {A1 : @El1 p Type0 Type1 A0}
  {x0 : El0 A0} {y0 : El0 A0} {q} (α : q ≤ p) :
  path A0 A1 x0 y0 -> path (α · A0) (α ⋅ A1) (α · x0) (α · y0).
Proof.
unshelve refine (fun x => _).
unshelve econstructor.
- exact (promote α ⋅ x.(path_f0)).
- exact (promote α ⋅ x.(path_f1)).
- refine (J_seqs _ _ (fun u _ => _ ≡ α ⋅ u) (srefl _) x0 (x.(path_s))).
- refine (J_seqs _ _ (fun u _ => _ ≡ α ⋅ u) (srefl _) y0 (x.(path_t))).
Defined.

Definition pathR {p} (A0 : @El0 p Type0) (A1 : @El1 p Type0 Type1 A0)
 (x0 : El0 A0) (y0 : El0 A0) :
 (forall q (α : q ≤ p), path (α · A0) (α ⋅ A1) (α · x0) (α · y0)) -> SProp :=
fun s => s ≡ fun q α => path_funct α (s p !).

Definition eq0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (y0 : El0 A0) :
  @El0 p Type0.
Proof.
unshelve refine (fun q α => mkYFT _ _ _ _).
- unshelve refine (fun r β => _).
  exact (path ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · x0) ((α ∘ β) · y0)).
- unshelve refine (fun r β s => _). simpl in s.
  exact (pathR ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · x0) ((α ∘ β) · y0) s).
- unshelve refine (fun r β b e l le l' => _).
  apply falso. (** TODO **)
Defined.

Definition eq1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (y0 : El0 A0) :
  @El1 p Type0 Type1 (eq0 A0 A1 x0 y0).
Proof.
unshelve refine (fun q α => _). reflexivity.
Defined.

Definition refl0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0) :
  @El0 p (eq0 A0 A1 x0 x0).
Proof.
unshelve refine (fun q α => _). simpl.
unshelve econstructor.
- exact ((α ∘ squish) ⋅ x0).
- exact ((α ∘ squish) ⋅ x1).
- reflexivity.
- reflexivity.
Defined.

Definition refl1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0) :
  @El1 p (eq0 A0 A1 x0 x0) (eq1 A0 A1 x0 x0) (refl0 A0 A1 x0 x1).
Proof.
unshelve refine (fun q α => _).
reflexivity.
Defined.

Definition contr_filler0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 b0))
  (e1 : El1 _ (eq1 A0 A1 a0 b0) e0)
  : El0 (squish ∘ squish ⋅ A0).
Proof.
Admitted.

Definition contr_filler1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 b0))
  (e1 : El1 _ (eq1 A0 A1 a0 b0) e0)
  : El1 _ (squish ∘ squish ⋅ A1) (contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1).
Proof.
Admitted.

Definition contr_eq0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 b0))
  (e1 : El1 _ (eq1 A0 A1 a0 b0) e0)
  : side_0 ⋅ (contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1) ≡ squish ⋅ a0.
Proof.
Admitted.

Definition contr_eq1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 b0))
  (e1 : El1 _ (eq1 A0 A1 a0 b0) e0)
  : promote side_0 ⋅ (contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1) ≡ squish ⋅ a0.
Proof.
Admitted.

Definition contr_eq2 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 b0))
  (e1 : El1 _ (eq1 A0 A1 a0 b0) e0)
  : promote side_1 ⋅ (contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1) ≡ (e0 p !).(path_f0).
Proof.
Admitted.

Definition decorated_contr_filler0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 b0))
  (e1 : El1 _ (eq1 A0 A1 a0 b0) e0)
  : El0 (squish ⋅ Sigma0 A0 A1
    (fun q α x0 x1 => eq0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) x0 q !)
    (fun q α x0 x1 => eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) x0 q !)).
Proof.
refine (fun q α => _) ; simpl.
unshelve econstructor.
- change (El0 (α ⋅ (side_1 ⋅ (squish ∘ squish ⋅ A0)))).
  exact (α ⋅ (side_1 ⋅ (contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1))).
- exact (α ⋅ (side_1 ⋅ (contr_filler1 A0 A1 a0 a1 b0 b1 e0 e1))).
- refine (fun r β => _) ; simpl.
  unshelve econstructor.
  + change (El0 (squish ∘ α ∘ β ∘ squish ⋅ A0)).
    change (El0 ((promote α) ∘ (promote β) ⋅ (squish ∘ squish ⋅ A0))).
    exact (promote α ∘ promote β ⋅ (contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1)).
  + exact (promote α ∘ promote β ⋅ (contr_filler1 A0 A1 a0 a1 b0 b1 e0 e1)).
  + change (α ∘ β ⋅ (side_0 ⋅ contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1) ≡ α ∘ β ⋅ (squish ⋅ a0)).
    refine (J_seqs _ _ (fun x _ => α ∘ β ⋅ x ≡ _) (srefl _) _
      (ssym (contr_eq0 A0 A1 a0 a1 b0 b1 e0 e1))).
  + reflexivity.
- refine (fun r0 β0 => _) ; simpl.
  reflexivity.
Defined.

Definition decorated_contr_filler1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 b0))
  (e1 : El1 _ (eq1 A0 A1 a0 b0) e0)
  : El1 _ (squish ⋅ Sigma1 A0 A1
    (fun q α x0 x1 => eq0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) x0 q !)
    (fun q α x0 x1 => eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) x0 q !))
    (decorated_contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1).
Proof.
refine (fun q α => _).
reflexivity.
Defined.

Definition singl_contr {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 b0))
  (e1 : El1 _ (eq1 A0 A1 a0 b0) e0)
  : El0 (eq0
    (Sigma0 A0 A1 (fun q α x0 x1 => eq0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) x0 q !) (fun q α x0 x1 => eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) x0 q !))
    (Sigma1 A0 A1 (fun q α x0 x1 => eq0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) x0 q !) (fun q α x0 x1 => eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) x0 q !))
    (dpair0 a0 a1 (refl0 A0 A1 a0 a1) (refl1 A0 A1 a0 a1))
    (dpair0 b0 b1 e0 e1)).
Proof.
refine (fun q α => _) ; simpl.
unshelve econstructor.
- exact (decorated_contr_filler0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1)).
- exact (decorated_contr_filler1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1)).
- apply ssym.
  unshelve refine (@seq_Sigma q
    _ _ (fun r β x0 x1 => eq0 (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (α ∘ β ⋅ a0) x0 r !) (fun r β x0 x1 => eq1 (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (α ∘ β ⋅ a0) x0 r !)
    _ (α ⋅ dpair1 a0 a1 (refl0 A0 A1 a0 a1) (refl1 A0 A1 a0 a1))
    _ (side_0 ⋅ decorated_contr_filler1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1))
    _ _).
  + unfold decorated_contr_filler0 ; unfold fst0 ; simpl.
    change (α ⋅ a0 ≡ side_1 ⋅ (promote side_0 ⋅ contr_filler0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1))).
    refine (J_seqs _ _ (fun x _ => α ⋅ a0 ≡ side_1 ⋅ x) (srefl _) _
      (ssym (contr_eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1)))).
  + unfold decorated_contr_filler0 ; unfold snd0 ; simpl.
    unfold seq_Sigma_transp ; unfold fst0 ; simpl.
    admit.
    (* RHS should be
    - first equated to (promote side_0 ⋅ contr_filler0) through contr_filler1
    - then equated to refl through contr_eq1 *)
- apply ssym.
  unshelve refine (@seq_Sigma q
    _ _ (fun r β x0 x1 => eq0 (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (α ∘ β ⋅ a0) x0 r !) (fun r β x0 x1 => eq1 (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (α ∘ β ⋅ a0) x0 r !)
    _ (α ⋅ dpair1 b0 b1 e0 e1)
    _ (side_1 ⋅ decorated_contr_filler1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1))
    _ _).
  + unfold decorated_contr_filler0 ; unfold fst0 ; simpl.
    change (α ⋅ b0 ≡ side_1 ⋅ (promote side_1 ⋅ contr_filler0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1))).
    refine (J_seqs _ _ (fun x _ => α ⋅ b0 ≡ side_1 ⋅ x) _ _
      (ssym (contr_eq2 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1)))).
    apply ssym.
    exact ((e0 q α).(path_t)).
  + unfold decorated_contr_filler0 ; unfold snd0 ; simpl.
    admit.
    (* RHS should be
    - first equated to (promote side_1 ⋅ contr_filler0) through contr_filler1
    - then equated to refl through contr_eq2 *)
Admitted.

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



(* etc etc *)
