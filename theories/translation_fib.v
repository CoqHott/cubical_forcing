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

Definition itype_out0_3 {A : Type} {B : A -> Type}
  {p : forall (a : A) (b : B a), nat}
  {X : forall (a : A) (b : B a), Type} {y z : forall (a : A) (b : B a), X a b}
  {x : forall (a : A) (b : B a), itype (p a b) (X a b) (y a b) (z a b)} :
  (fun a b => itype_out (x a b) side0) ≡ y.
Proof.
Admitted.

Definition itype_out1_2 {p} {A : Type} {B : A -> SProp}
  {X : forall (a : A) (b : B a), Type} {y z : forall (a : A) (b : B a), X a b}
  {x : forall (a : A) (b : B a), itype p (X a b) (y a b) (z a b)} :
  (fun a b => itype_out (x a b) side1) ≡ z.
Proof.
Admitted.

Definition itype_out1_3 {A : Type} {B : A -> Type}
  {p : forall (a : A) (b : B a), nat}
  {X : forall (a : A) (b : B a), Type} {y z : forall (a : A) (b : B a), X a b}
  {x : forall (a : A) (b : B a), itype (p a b) (X a b) (y a b) (z a b)} :
  (fun a b => itype_out (x a b) side1) ≡ z.
Proof.
Admitted.


(* With itypes, a direct proof of funext should be possible.
   It is also possible to define it through another equivalent path type
   see translation_fib_path.v for a working version
 *)

Definition eq_funext {p}
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
  refine (@itype_out r (yft0 (B0 r (α ∘ squish ∘ β)) r !)
    (f0 r (α ∘ squish ∘ β) x0 x1) (g0 r (α ∘ squish ∘ β) x0 x1)
    _ (antisquish ∘ β)).
  refine (J_seq _ _ (fun X _ => itype _ _ (X r !) _) _ _ ((h0 r (α ∘ squish ∘ β) x0 x1).(ce_s))).
  refine (J_seq _ _ (fun X _ => itype _ _ _ (X r !)) _ _ ((h0 r (α ∘ squish ∘ β) x0 x1).(ce_t))).
  refine (@itype_in r (yft0 (B0 r (α ∘ squish ∘ β)) r !) (fun αi => (h0 r (α ∘ squish ∘ β) x0 x1).(ce_f0) r (merge ! αi))).
- refine (fun r β x0 x1 => _). admit.
- simpl. (* use the cbv property for itype_out *) admit.
- simpl. (* use the cbv property for itype_out *) admit.
Abort.

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
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0) :
  El0 (app0 P0 b0 b1).
Proof.
refine (fun q α => _).
(* this is the family above the path *)
unshelve refine (let Q0 : @El0 (S q) Type0 := _ in _).
{ exact (@app0 (S q) _ _ Type0 Type1 (α ∘ squish ⋅ P0) (ce_f0 (e0 q α)) (ce_f1 (e0 q α))). }
unshelve refine (let Q1 : El1 Type0 Type1 Q0 := _ in _).
{ exact (@app1 (S q) _ _ Type0 Type1 (α ∘ squish ⋅ P0) (α ∘ squish ⋅ P1) (ce_f0 (e0 q α)) (ce_f1 (e0 q α))). }
(* now we inhabit it on side_0 *)
unshelve refine (let s0 : El0 (side_0 ⋅ Q0) := _ in _).
{ refine (fun r β => _). unfold Q0 ; unfold app0 ; simpl.
  refine (J_seq _ _
    (fun X E => yft0 (P0 r (α ∘ β) (β ⋅ X)
      (J_seqs _ _ (fun Y _ => El1 (α ∘ β ⋅ A0) (α ∘ β ⋅ A1) (β ⋅ Y)) (α ∘ β ⋅ a1) X E))
      r !)
    _ _ (ssym (ce_s (e0 q α)))). simpl.
  refine (x0 r (α ∘ β)). }
unshelve refine (let s1 : El1 (side_0 ⋅ Q0) (side_0 ⋅ Q1) s0 := _ in _).
{ refine (fun r β => _).
  unfold Q0 ; unfold Q1 ; unfold app0 ; unfold app1 ; unfold s0 ; simpl.
  refine (J_seq _ _ (fun X' E' => (fun (Y' : El1 (α ⋅ A0) (α ⋅ A1) X') =>
    yft1 (P0 r (α ∘ β) (β ⋅ X') (β ⋅ Y')) r !
    (fun (r0 : nat) (β0 : r0 ≤ r) =>
     cast0
       (fun (r1 : nat) (β1 : r1 ≤ q) => P0 r1 (α ∘ β1) (β1 ⋅ X') (β1 ⋅ Y'))
       (fun (r1 : nat) (β1 : r1 ≤ q) => P1 r1 (α ∘ β1) (β1 ⋅ X') (β1 ⋅ Y')) β β0
       (J_seq _ _
          (fun X (E : α ⋅ a0 ≡ X) =>
           yft0
             (P0 r0 (α ∘ (β ∘ β0)) (β ∘ β0 ⋅ X)
                (J_seqs _ _
                   (fun Y (_ : α ∘ ! ⋅ a0 ≡ Y) => El1 (α ∘ (β ∘ β0) ⋅ A0) (α ∘ (β ∘ β0) ⋅ A1) (β ∘ β0 ⋅ Y))
                   (α ∘ (β ∘ β0) ⋅ a1) X E)) r0 !) (x0 r0 (α ∘ (β ∘ β0))) X' E'))) (J_seqs _ _ (fun Z _ => El1 (α ⋅ A0) (α ⋅ A1) Z) (α ⋅ a1) X' E'))
   _ _ (ssym (ce_s (e0 q α)))). simpl.
  refine (x1 r (α ∘ β)). }
(* now we use fibrancy of Q to inhabit it on side_1 *)
unshelve refine (let t0 : El0 (side_1 ⋅ Q0) := _ in _).
{ admit. }
unshelve refine (let t1 : El1 (side_1 ⋅ Q0) (side_1 ⋅ Q1) t0 := _ in _).
{ admit. }
(* and use t to conclude *)
unfold app0 ; simpl.
pose proof (ce_t (e0 q α)).
refine (J_seq _ _
  (fun X E => yft0 (P0 q α X
    (J_seqs _ _ (fun Y _ => El1 (α ⋅ A0) (α ⋅ A1) Y) (side_1 ⋅ ce_f1 (e0 q α)) X E))
      q !)
    _ _ (ce_t (e0 q α))). simpl.
refine (t0 q !).
Admitted.

Definition path_transp1 {p}
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
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0) :
  El1 (app0 P0 b0 b1) (app1 P1 b0 b1) (path_transp0 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1).
Proof.
refine (fun q α => _).
Admitted.

Definition weakunivalence0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0)
  : El0 (eq0 Type0 Type1 A0 A1 B0 B1).
Admitted.
