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
    exteq_ytEl (ytEl_funct α le_el) (e.(pe_el) q ((lidface l) ∘ α) Hα) ;
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
  forall q (α : q ≤ p),
    seq@{k} (s q α) (yft_funct α (s p !)).

Definition cast0 {p : ℙ}
  (A0 : forall q (α : q ≤ p), yft q)
  (A1 : forall q (α : q ≤ p), yftR (α · A0))
  {q} (α : q ≤ p) {r} (β : r ≤ q) :
  (A0 r (α ∘ β)).(yft0) r ! -> (A0 q α).(yft0) r β.
Proof.
refine (fun x => _).
refine (J_seq _ _ (fun a _ => a.(yft0) r !) x _ (A1 q α r β)).
Defined.

(* Definition yftR@{i j k} {p : ℙ} (s : forall q : nat, q ≤ p -> yft@{i j} q) : SProp :=
  forall q (α : q ≤ p),
    seq@{k} ((s q α).(yft0) q !) ((s p !).(yft0) q α).

Definition cast0 {p : ℙ}
  (A0 : forall q (α : q ≤ p), yft q)
  (A1 : forall q (α : q ≤ p), yftR (α · A0))
  {q} (α : q ≤ p) {r} (β : r ≤ q) :
  (A0 r (α ∘ β)).(yft0) r ! -> (A0 q α).(yft0) r β.
Proof.
refine (fun x => _).
refine (J_seq _ _ (fun a _ => a) x _ (A1 q α r β)).
Defined. *)

(* Definition yftR@{i j k} {p : ℙ} (s : forall q : nat, q ≤ p -> yft@{i j} q) : SProp :=
  seq@{k} s (fun q α => yft_funct@{i j} α (s p !)). *)

(* Definition cast0 {p : ℙ}
  (A0 : forall q (α : q ≤ p), yft q)
  (A1 : forall q (α : q ≤ p), yftR (α · A0))
  {q} (α : q ≤ p) {r} (β : r ≤ q) :
  (A0 r (α ∘ β)).(yft0) r ! -> (A0 q α).(yft0) r β.
Proof.
refine (fun x => _).
refine (J_seq _ (α ⋅ A0) (fun a _ => (a r β).(yft0) r !) x _ (A1 q α)).
Defined. *)

(* Definition seq_yftAlt {p : ℙ}
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
Defined. *)

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
       yt1 := fun q (_ : q ≤ p) s => yftR@{i j k} s ; |} domain.

Definition tubeYft@{i j k l} {p : ℙ} (b : cofib p) :=
  tubeEl@{k l}
    {| yt0 := fun q (_ : q ≤ S p) => yft@{i j} q ;
       yt1 := fun q (_ : q ≤ S p) s => yftR@{i j k} s ; |} b.

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
    * refine (if (tubeface b ((lidface l') ∘ α)) then _ else _).
      admit.
      admit. (* refine (fun r β => tubeGlue@{i j k l} t lt l' (α ∘ β)). *)
    * admit. (*  refine (fun r β => tubeGlueR@{i j k l} t lt l' (α ∘ β)). *)
    * admit. (* refine (fun r β => tubeGlueFib t lt l' (α ∘ β)). *)
  + refine (fun q α r β => _). simpl.
    admit.
- unshelve refine (fun q α Hα r β => _) ; simpl.
  reflexivity.
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
refine (fun q α => _). reflexivity.
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
    apply sfalso.
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
refine (fun q α r β => _).
reflexivity.
Defined.

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
+ refine (fun q α => _).
  apply falso.
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


(* first version of equality *)

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
unshelve refine (fun q α => mkYFT _ _ _ _).
- unshelve refine (fun r β => _).
  exact (cube_eq ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · x0) ((α ∘ β) · y0)).
- unshelve refine (fun r β s => _). simpl in s.
  exact (cube_eqR ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · x0) ((α ∘ β) · y0) s).
- unshelve refine (fun r β b e l le l' => _).
  apply falso. (** TODO **)
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

(* Definition eq_funext {p}
(A0 : @El0 p Type0)
(A1 : @El1 p Type0 Type1 A0)
(B0 : @El0 p Type0)
(B1 : @El1 p Type0 Type1 B0)
(f0 : El0 (Arr0 A0 A1 B0 B1))
(f1 : El1 _ (Arr1 A0 A1 B0 B1) f0)
(g0 : El0 (Arr0 A0 A1 B0 B1))
(g1 : El1 _ (Arr1 A0 A1 B0 B1) g0)
(h0 : El0 (Prod0 A0 A1
  (fun q α x0 x1 => eq0 (α ⋅ B0) (α ⋅ B1)
    (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
    (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
  (fun q α x0 x1 => eq1 (α ⋅ B0) (α ⋅ B1)
    (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
    (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
  ))
(h1 : El1 _ (Prod1 A0 A1
  (fun q α x0 x1 => eq0 (α ⋅ B0) (α ⋅ B1)
    (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
    (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
  (fun q α x0 x1 => eq1 (α ⋅ B0) (α ⋅ B1)
    (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
    (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
  ) h0)
: El0 (eq0 (Arr0 A0 A1 B0 B1) (Arr1 A0 A1 B0 B1) f0 f1 g0 g1).
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β x0 x1 => _). 
  pose proof ((h0 r (α ∘ squish ∘ β) x0 x1).(ce_f0)). change (El0 (α ∘ squish ∘ β ∘ squish ⋅ B0)) in X.
  pose proof ((h1 r (α ∘ squish ∘ β) x0 x1)). simpl in H. unfold cube_eqR in H. 
  unfold cast0 in H ; simpl in H.
  unfold ce_funct in H.  *)


(* Axioms for interval-types, à la CubicalTT *)

Definition side0 {p} : p ≤ 1.
Proof.
unshelve econstructor.
- refine (fun c n => false).
- refine (fun c d Hcd n => _). easy.
Defined.

Definition side1 {p} : p ≤ 1.
Proof.
unshelve econstructor.
- refine (fun c n => true).
- refine (fun c d Hcd n => _). easy.
Defined.

Definition itype (p : ℙ) (A : Type) (x y : A) : Type.
Admitted.

Definition itype_in {p} {A : Type} (z : p ≤ 1 -> A) :
  itype p A (z side0) (z side1).
Admitted.

Definition itype_out {p} {A : Type} {x y : A} :
  itype p A x y -> p ≤ 1 -> A.
Admitted.

Definition itype_inout :
  (fun p A (x : p ≤ 1 -> A) y => itype_out (itype_in x) y) ≡ fun p A x y => x y.
Admitted.

Definition itype_out0 {p} {A : Type}
  {X : A -> Type} {y z : forall a : A, X a}
  {x : forall a : A, itype p (X a) (y a) (z a)} :
  (fun a => itype_out (x a) side0) ≡ y.
Admitted.

Definition itype_out0_2 {p} {A : Type} {B : A -> SProp}
  {X : forall (a : A) (b : B a), Type} {y z : forall (a : A) (b : B a), X a b}
  {x : forall (a : A) (b : B a), itype p (X a b) (y a b) (z a b)} :
  (fun a b => itype_out (x a b) side0) ≡ y.
Proof.
Admitted.

Definition itype_out1_2 {p} {A : Type} {B : A -> SProp}
  {X : forall (a : A) (b : B a), Type} {y z : forall (a : A) (b : B a), X a b}
  {x : forall (a : A) (b : B a), itype p (X a b) (y a b) (z a b)} :
  (fun a b => itype_out (x a b) side1) ≡ z.
Proof.
Admitted.



(* translation of equality, CubicalTT-style *)

Definition path0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
  (y0 : El0 A0)
  (y1 : El1 A0 A1 y0)
: @El0 p Type0.
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β => _).
  exact (itype r ((A0 r (α ∘ β)).(yft0) r !)
    (x0 r (α ∘ β)) (y0 r (α ∘ β))).
- refine (fun r β s => _). simpl in s.
  refine
  (forall (αi : r ≤ 1),
  (A0 r (α ∘ β)).(yft1) r !
  (fun r0 β0 => cast0 A0 A1 (α ∘ β) β0
    _
  )).
  refine (itype_out (s r0 β0) (αi ∘ β0)).
- refine (fun r β => _).
  apply falso.
Defined.

Definition path1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
  (y0 : El0 A0)
  (y1 : El1 A0 A1 y0)
: @El1 p Type0 Type1 (path0 A0 A1 x0 x1 y0 y1).
Proof.
refine (fun q α r β => _).
reflexivity.
Defined.

Definition path_refl0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
: El0 (path0 A0 A1 x0 x1 x0 x1).
Proof.
refine (fun q α => _). simpl.
exact (itype_in (fun _ => x0 q α)).
Defined.

Definition path_refl1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
: El1 _ (path1 A0 A1 x0 x1 x0 x1) (path_refl0 A0 A1 x0 x1).
Proof.
refine (fun q α αi => _).
unfold path_refl0 ; simpl. unfold cast0 ; simpl.
refine (J_seqs _ (fun p A x y => x y)
  (fun x _ => yft1 (A0 q α) q !
    (fun r β => J_seq (yft r) (A0 r (α ∘ β))
      (fun a _ => yft0 a r !)
      (x r (yft0 (A0 r (α ∘ β)) r !) (fun _ => x0 r (α ∘ β)) (αi ∘ β))
      (yft_funct β (A0 q α)) (A1 q α r β)
    )
  )
  _ (fun p A (x : p ≤ 1 -> A) y => itype_out (itype_in x) y)
  (ssym itype_inout)).
refine (x1 q α).
Defined.

Definition path_transp0 {p}
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
  (e0 : El0 (path0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (path1 A0 A1 a0 a1 b0 b1) e0) :
  El0 (app0 P0 b0 b1).
Proof.
refine (fun q α => _).
pose proof (e0 q α) as e0'. simpl in e0'.
Admitted.

Definition path_glueing0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0)
: @El0 p (path0 Type0 Type1 A0 A1 B0 B1).
Proof.
refine (fun q α => _). change (itype q (yft q) (A0 q α) (B0 q α)).
assert ((q ≤ 1) -> yft q) as e.
{ apply falso. }
assert (e side0 ≡ A0 q α). apply sfalso. rewrite <- H.
assert (e side1 ≡ B0 q α). apply sfalso. rewrite <- H0.
exact (itype_in e).
Defined.

Definition path_glueing1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0)
: @El1 p _ (path1 Type0 Type1 A0 A1 B0 B1) (path_glueing0 A0 A1 B0 B1).
Proof.
refine (fun q α αi r β => _). unfold cast0 ; simpl.
unfold yft_funct ; simpl.
(* that much should be easy *)
Admitted.

Definition path_funext0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0)
  (f0 : El0 (Arr0 A0 A1 B0 B1))
  (f1 : El1 _ (Arr1 A0 A1 B0 B1) f0)
  (g0 : El0 (Arr0 A0 A1 B0 B1))
  (g1 : El1 _ (Arr1 A0 A1 B0 B1) g0)
  (h0 : El0 (Prod0 A0 A1
    (fun q α x0 x1 => path0 (α ⋅ B0) (α ⋅ B1)
      (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
      (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
    (fun q α x0 x1 => path1 (α ⋅ B0) (α ⋅ B1)
      (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
      (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
    ))
  (h1 : El1 _ (Prod1 A0 A1
    (fun q α x0 x1 => path0 (α ⋅ B0) (α ⋅ B1)
      (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
      (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
    (fun q α x0 x1 => path1 (α ⋅ B0) (α ⋅ B1)
      (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
      (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
    ) h0)
: El0 (path0 (Arr0 A0 A1 B0 B1) (Arr1 A0 A1 B0 B1) f0 f1 g0 g1).
Proof.
refine (fun q α => _).
change (itype q (forall x0 : El0 (α ⋅ A0), El1 (α ⋅ A0) (α ⋅ A1) x0 -> yft0 (B0 q α) q !) (f0 q α) (g0 q α)).
assert ((fun x0 x1 => itype_out (h0 q α x0 x1) side0) ≡ f0 q α) as H0.
{ eapply itype_out0_2. }
assert ((fun x0 x1 => itype_out (h0 q α x0 x1) side1) ≡ g0 q α) as H1.
{ eapply itype_out1_2. }
refine (J_seq _ _ (fun x _ => itype q _ x _) _ _ H0).
refine (J_seq _ _ (fun x _ => itype q _ _ x) _ _ H1).
refine (itype_in (fun αi x0 x1 => itype_out (h0 q α x0 x1) αi)).
Defined.

Definition path_funext1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0)
  (f0 : El0 (Arr0 A0 A1 B0 B1))
  (f1 : El1 _ (Arr1 A0 A1 B0 B1) f0)
  (g0 : El0 (Arr0 A0 A1 B0 B1))
  (g1 : El1 _ (Arr1 A0 A1 B0 B1) g0)
  (h0 : El0 (Prod0 A0 A1
    (fun q α x0 x1 => path0 (α ⋅ B0) (α ⋅ B1)
      (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
      (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
    (fun q α x0 x1 => path1 (α ⋅ B0) (α ⋅ B1)
      (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
      (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
    ))
  (h1 : El1 _ (Prod1 A0 A1
    (fun q α x0 x1 => path0 (α ⋅ B0) (α ⋅ B1)
      (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
      (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
    (fun q α x0 x1 => path1 (α ⋅ B0) (α ⋅ B1)
      (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
      (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1) q !)
    ) h0)
: El1 _ (path1 (Arr0 A0 A1 B0 B1) (Arr1 A0 A1 B0 B1) f0 f1 g0 g1)
  (path_funext0 A0 A1 B0 B1 f0 f1 g0 g1 h0 h1).
Proof.
refine (fun q α αi x0 x1 => _).
unfold cast0 ; simpl.
unfold path_funext0 ; simpl.
(* essentiellement on veut
yft1 (B0 q α) q !
  (fun r β => itype_out (itype_in (fun αi x0 x1 => itype_out (h0 r (α ∘ β) (β ⋅ x0) (β ⋅ x1)) (αi ∘ β))))
soit, en simplifiant,
yft1 (B0 q α) q !
  (fun r β => itype_out (h0 r (α ∘ β) (β ⋅ x0) (β ⋅ x1)) (αi ∘ β))
 *)
pose proof (h1 q α x0 x1 αi) as H ; simpl in H.
unfold cast0 in H ; simpl in H.
(* et on obtient
yft1 (B0 q α) q !
  (fun r β => itype_out (h0 r (α ∘ β) (β ⋅ x0) (β ⋅ x1)) (αi ∘ β))
Donc c'est gagné, mais j'ai pas envie de l'écrire
*)
Admitted.

Definition contr_filler {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (path0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (path1 A0 A1 a0 a1 b0 b1) e0)
  : (p ≤ 1) -> (p ≤ 1) -> yft0 (A0 p !) p !.
Proof.
Admitted.

Definition contr_filler_side0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (path0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (path1 A0 A1 a0 a1 b0 b1) e0)
  (αi : p ≤ 1)
  : contr_filler A0 A1 a0 a1 b0 b1 e0 e1 αi side0 ≡ a0 p !.
Proof.
Admitted.

Definition singl_contr_aux {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (path0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (path1 A0 A1 a0 a1 b0 b1) e0)
  : (p ≤ 1) -> (SigmaT A0 A1 (fun q α x0 x1 => path0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => path1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !)).
Proof.
refine (fun αi => _).
unshelve econstructor.
- refine (fun q α => _).
  refine (contr_filler (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1) (αi ∘ α) (side1 ∘ α)).
- refine (fun q α => _).
  (* TODO *)
  apply sfalso.
- refine (fun q α => _) ; simpl.
  refine (J_seq _ _ (fun x _ => itype q _ x _) _ _ (contr_filler_side0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1) (αi ∘ α))).
  refine (itype_in (contr_filler (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1) (αi ∘ α))).
- refine (fun q α αi => _). unfold cast0 ; simpl.
  (* TODO *)
  apply sfalso.
Defined.

Definition singl_contr_aux_side0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (path0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (path1 A0 A1 a0 a1 b0 b1) e0)
  : singl_contr_aux A0 A1 a0 a1 b0 b1 e0 e1 side0 ≡
  @dpair0 p A0 A1 (fun q α x0 x1 => path0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => path1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) a0 a1 (path_refl0 A0 A1 a0 a1) (path_refl1 A0 A1 a0 a1) p !.
Proof.
unfold singl_contr_aux ; simpl.
Admitted.

Definition singl_contr_aux_side1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (path0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (path1 A0 A1 a0 a1 b0 b1) e0)
  : singl_contr_aux A0 A1 a0 a1 b0 b1 e0 e1 side1 ≡
  @dpair0 p A0 A1 (fun q α x0 x1 => path0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => path1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) b0 b1 e0 e1 p !.
Proof.
Admitted.

Definition singl_contr0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (path0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (path1 A0 A1 a0 a1 b0 b1) e0)
  : El0 (path0
    (Sigma0 A0 A1 (fun q α x0 x1 => path0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => path1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !))
    (Sigma1 A0 A1 (fun q α x0 x1 => path0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => path1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !))
    (dpair0 a0 a1 (path_refl0 A0 A1 a0 a1) (path_refl1 A0 A1 a0 a1))
    (dpair1 a0 a1 (path_refl0 A0 A1 a0 a1) (path_refl1 A0 A1 a0 a1))
    (dpair0 b0 b1 e0 e1)
    (dpair1 b0 b1 e0 e1)).
Proof.
refine (fun q α => _). simpl.
refine (J_seq _ _ (fun x _ => itype q _ x (dpair0 b0 b1 e0 e1 q α)) _ _ (singl_contr_aux_side0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1))).
refine (J_seq _ _ (fun x _ => itype q _ _ x) _ _ (singl_contr_aux_side1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1))).
refine (itype_in (singl_contr_aux (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1))).
Defined.

Definition singl_contr1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (path0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (path1 A0 A1 a0 a1 b0 b1) e0)
  : El1 _ (path1
    (Sigma0 A0 A1 (fun q α x0 x1 => path0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => path1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !))
    (Sigma1 A0 A1 (fun q α x0 x1 => path0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => path1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !))
    (dpair0 a0 a1 (path_refl0 A0 A1 a0 a1) (path_refl1 A0 A1 a0 a1))
    (dpair1 a0 a1 (path_refl0 A0 A1 a0 a1) (path_refl1 A0 A1 a0 a1))
    (dpair0 b0 b1 e0 e1)
    (dpair1 b0 b1 e0 e1))
    (singl_contr0 A0 A1 a0 a1 b0 b1 e0 e1).
Proof.
refine (fun q α αi => _) ; simpl.
unfold SigmaR ; unfold cast0 ; simpl.
(* idk, prolly gonna work when i fill out the details *)
Admitted.

(* comparing eq and path *)

Definition compare0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
  (y0 : El0 A0)
  (y1 : El1 A0 A1 y0)
  (e0 : El0 (path0 A0 A1 x0 x1 y0 y1))
  (e1 : El1 _ (path1 A0 A1 x0 x1 y0 y1) e0)
  : El0 (eq0 A0 A1 x0 x1 y0 y1).
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β => _).
  refine (itype_out (e0 r (α ∘ squish ∘ β)) (antisquish ∘ β)).
- refine (fun r β => _).
  refine (e1 r (α ∘ squish ∘ β) (antisquish ∘ β)).
- change ((fun r β => itype_out (e0 r (α ∘ β)) (side0)) ≡ α ⋅ x0).
  apply sfalso. (* easy *)
- change ((fun r β => itype_out (e0 r (α ∘ β)) (side1)) ≡ α ⋅ y0).
  apply sfalso. (* easy *)
Defined.

Definition compare1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
  (y0 : El0 A0)
  (y1 : El1 A0 A1 y0)
  (e0 : El0 (path0 A0 A1 x0 x1 y0 y1))
  (e1 : El1 _ (path1 A0 A1 x0 x1 y0 y1) e0)
  : El1 _ (eq1 A0 A1 x0 x1 y0 y1) (compare0 A0 A1 x0 x1 y0 y1 e0 e1).
Proof.
refine (fun q α => _). simpl. unfold cube_eqR.
reflexivity.
Defined.

Definition anticompare0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
  (y0 : El0 A0)
  (y1 : El1 A0 A1 y0)
  (e0 : El0 (eq0 A0 A1 x0 x1 y0 y1))
  (e1 : El1 _ (eq1 A0 A1 x0 x1 y0 y1) e0)
  : El0 (path0 A0 A1 x0 x1 y0 y1).
Proof.
refine (fun q α => _). simpl.
assert (x0 q α ≡ (e0 p !).(ce_f0) q (merge α side0)) as H0.
{ refine (J_seqs _ _ (fun x _ => x q α ≡ _) (srefl _) x0 ((e0 p !).(ce_s))). }
assert (y0 q α ≡ (e0 p !).(ce_f0) q (merge α side1)) as H1.
{ refine (J_seqs _ _ (fun x _ => x q α ≡ _) (srefl _) y0 ((e0 p !).(ce_t))). }
refine (J_seq _ _ (fun x _ => itype q _ x _) _ _ (ssym H0)).
refine (J_seq _ _ (fun x _ => itype q _ _ x) _ _ (ssym H1)).
refine (@itype_in q (yft0 (A0 q α) q !) (fun αi => (e0 p !).(ce_f0) q (merge α αi))).
Defined.

Definition anticompare1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (x0 : El0 A0)
  (x1 : El1 A0 A1 x0)
  (y0 : El0 A0)
  (y1 : El1 A0 A1 y0)
  (e0 : El0 (eq0 A0 A1 x0 x1 y0 y1))
  (e1 : El1 _ (eq1 A0 A1 x0 x1 y0 y1) e0)
  : El1 _ (path1 A0 A1 x0 x1 y0 y1) (anticompare0 A0 A1 x0 x1 y0 y1 e0 e1).
Proof.
refine (fun q α αi => _). unfold cast0 ; simpl.
unfold anticompare0.
Admitted.


