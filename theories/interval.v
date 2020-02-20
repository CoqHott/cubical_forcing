From Theories Require Import category.
From Theories Require Import translation.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(* Yoneda presheaf *)

Inductive yoR (l : ℙ) (p : ℙ) : (forall q (α : q ≤ p), q ≤ l) -> SProp :=
| yoR_cons : forall (β : p ≤ l), yoR l p (fun q α => β ∘ α).

Definition yoᶠ (l : ℙ) {p} : @El p Typeᶠ.
Proof.
unshelve refine (fun q α => mkTYPE _ _ _).
+ unshelve refine (fun r β => r ≤ l).
+ unshelve refine (fun f => yoR l q f). 
Defined.

Definition yoε (l : ℙ) {p : ℙ} : @Elε p Typeᶠ Typeε (yoᶠ l).
Proof.
unfold Elε; cbn.
reflexivity.
Defined.

(* Interval with endpoints *)

Definition Iᶠ {p} : @El p Typeᶠ := yoᶠ 1.
Definition Iε {p} : @Elε p Typeᶠ Typeε Iᶠ := yoε 1.

Definition cst_0 (p : ℙ) : p ≤ 1.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
+ refine (fun _ _ => false).
+ unshelve refine (fun _ _ _ _ => sI).
Defined.

Definition i0ᶠ {p : ℙ} : @El p Iᶠ.
Proof.
refine (fun q β => cst_0 q).
Defined.

Definition i0ε {p : ℙ} : @Elε p Iᶠ Iε i0ᶠ.
Proof.
refine (fun q α => yoR_cons 1 q (cst_0 q)).
Defined.

Definition cst_1 (p : ℙ) : p ≤ 1.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
+ refine (fun _ _ => true).
+ unshelve refine (fun _ _ _ _ => sI).
Defined.

Definition i1ᶠ {p : ℙ} : @El p Iᶠ.
Proof.
refine (fun q β => cst_1 q).
Defined.

Definition i1ε {p : ℙ} : @Elε p Iᶠ Iε i1ᶠ.
Proof.
refine (fun q α => yoR_cons 1 q (cst_1 q)).
Defined.

(* Axioms on the interval *)
(* TODO *)

(** Axiom 2 **)

Lemma ap_10 {A B} {f g : forall a  : A, B a} (x : A) (e : f = g) : f x = g x.
Proof.
  destruct e. reflexivity.
Defined.

Lemma neq_cst {p q} (α : p ≤ q) : α · i0ᶠ = α · i1ᶠ -> empty.
Proof.
  intro H.
  unfold le_cmp in H.
  apply (ap_10 p) in H.
  cbn in H.
  apply (ap_10 !) in H. cbn in H. unfold i0ᶠ, i1ᶠ in H.
  unfold cst_0, cst_1 in H. cbn in H.
  apply (f_equal arr) in H. cbn in H.
  apply (ap_10 (fun _ => true)) in H. cbn in H.
  unshelve eapply (ap_10 _) in H.
  { unshelve econstructor.
    - exact 0.
    - constructor.
  }
  cbn in H.
  discriminate.
Defined.

Definition ax2ᶠ {p} : @El p (Arr _ (eqε _ _ i0ᶠ i0ε i1ᶠ i1ε) _ emptyε).
Proof.
  intros q α.
  intro H.
  assert (t := H q !).
  intro H1. cbn.
  cbn in t. repeat change (?f ∘ !) with f in *.
  apply (neq_cst α).
  destruct t. reflexivity.
Defined.

Definition ax2ε {p} : @Elε p _ (Arrε _ (eqε _ _ i0ᶠ i0ε i1ᶠ i1ε) _ emptyε) ax2ᶠ.
Proof.
  intros q α.
  cbn.
  intro H.
  assert (t := H q !).
  intro H1. cbn.
  cbn in t.
  repeat change (?f ∘ !) with f in *.
  apply empty_sind.
  apply (neq_cst α).
  destruct t. reflexivity.
Defined.
  
