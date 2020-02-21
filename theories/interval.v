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

(* Interval *)

Definition Iᶠ {p} : @El p Typeᶠ := yoᶠ 1.
Definition Iε {p} : @Elε p Typeᶠ Typeε Iᶠ := yoε 1.

Definition seq_I {p : ℙ}
    {i : @El p Iᶠ} {iε : Elε Iᶠ Iε i}
    {j : @El p Iᶠ} {jε : Elε Iᶠ Iε j} :
    i p ! ≡ j p ! -> i ≡ j.
Proof.
intro H.
pose proof (iε p !) as Hi. inversion Hi as [α Hα].
cbn in Hα. change (! · i) with i in Hα.
pose proof (jε p !) as Hj. inversion Hj as [β Hβ].
cbn in Hβ. change (! · j) with j in Hβ.
rewrite <- Hα. rewrite <- Hβ.
rewrite <- Hα in H. change (α ∘ !) with α in H.
rewrite <- Hβ in H. change (β ∘ !) with β in H.
destruct H. refine (srefl _).
Defined.

(* Interval endpoint i0 *)

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

(* Interval endpoint i1 *)

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

(* Axiom 1 : the interval is connected *)

Definition isdecᶠ {p : ℙ}
    (φ : @El p (Arr Iᶠ Iε Typeᶠ Typeε))
    (φε : Elε _ (Arrε Iᶠ Iε Typeᶠ Typeε) φ) :
    @El p (Arr Iᶠ Iε Typeᶠ Typeε) :=
(lamᶠ (fun q α i iε =>
    sumᶠ (appᶠ (α · φ) i iε) (appε (α · φε) i iε)
         (Arr _ (appε (α · φε) i iε) emptyᶠ emptyε)
         (Arrε (appᶠ (α · φ) i iε) (appε (α · φε) i iε) emptyᶠ emptyε))).

Definition isdecε {p : ℙ}
    (φ : @El p (Arr Iᶠ Iε Typeᶠ Typeε))
    (φε : Elε _ (Arrε Iᶠ Iε Typeᶠ Typeε) φ) :
    Elε _ (Arrε Iᶠ Iε Typeᶠ Typeε) (isdecᶠ φ φε) :=
(lamε (fun q α i iε =>
    sumε (appᶠ (α · φ) i iε) (appε (α · φε) i iε)
         (Arr _ (appε (α · φε) i iε) emptyᶠ emptyε)
         (Arrε (appᶠ (α · φ) i iε) (appε (α · φε) i iε) emptyᶠ emptyε))).

Definition negᶠ {p : ℙ}
    (φ : @El p (Arr Iᶠ Iε Typeᶠ Typeε))
    (φε : Elε _ (Arrε Iᶠ Iε Typeᶠ Typeε) φ) :
    @El p (Arr Iᶠ Iε Typeᶠ Typeε) :=
(lamᶠ (fun q α i iε =>
    Arr (appᶠ (α · φ) i iε) (appε (α · φε) i iε)
        emptyᶠ emptyε)).

Definition negε {p : ℙ}
    (φ : @El p (Arr Iᶠ Iε Typeᶠ Typeε))
    (φε : Elε _ (Arrε Iᶠ Iε Typeᶠ Typeε) φ) :
    Elε _ (Arrε Iᶠ Iε Typeᶠ Typeε) (negᶠ φ φε) :=
(lamε (fun q α i iε =>
    Arrε (appᶠ (α · φ) i iε) (appε (α · φε) i iε)
        emptyᶠ emptyε)).

Definition hot_aux {p : ℙ}
    (i : @El p Iᶠ) (iε : Elε Iᶠ Iε i) :
    S p ≤ 1.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
- unshelve refine (fun c => if (c finzero) then _ else _).
  + refine ((i p !).(arr) (fun n => c (finsucc n))).
  + refine (fun _ => false).
- intros c d Hcd.
  remember (c finzero) as c0. remember (d finzero) as d0.
  destruct c0 ; destruct d0.
  + apply ((i p !).(eps_arr)).
    intro n. exact (Hcd (finsucc n)).
  + specialize (Hcd finzero).
    rewrite <- Heqc0 in Hcd. rewrite <- Heqd0 in Hcd. destruct Hcd.
  + easy.
  + easy.
Defined.

Definition homotopy_to_0ᶠ {p : ℙ}
    (i : @El p Iᶠ) (iε : Elε Iᶠ Iε i) :
    @El (S p) Iᶠ.
Proof.
unshelve refine (fun q α => (hot_aux i iε) ∘ α).
Defined.

Definition homotopy_to_0ε {p : ℙ}
    (i : @El p Iᶠ) (iε : Elε Iᶠ Iε i) :
    Elε Iᶠ Iε (homotopy_to_0ᶠ i iε).
Proof.
unshelve refine (fun q α => _).
refine (yoR_cons 1 q (hot_aux i iε ∘ α)).
Defined.

Definition side_0 {p : ℙ} : p ≤ S p.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
- unshelve refine (fun c n => _).
  destruct n as [n nε]. destruct n as [|n'].
  + exact false.
  + apply c. unshelve refine (mkFinset p n' _).
    apply le_to_sle. apply le_S_n. apply sle_to_le. exact nε.
- intros c d Hcd n. destruct n as [n nε]. destruct n.
  + exact sI.
  + refine (Hcd _).
Defined.

Definition side_1 {p : ℙ} : p ≤ S p.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
- unshelve refine (fun c n => _).
  destruct n as [n nε]. destruct n as [|n'].
  + exact true.
  + apply c. unshelve refine (mkFinset p n' _).
    apply le_to_sle. apply le_S_n. apply sle_to_le. exact nε.
- intros c d Hcd n. destruct n as [n nε]. destruct n.
  + exact sI.
  + refine (Hcd _).
Defined.

Definition restriction_0 {p : ℙ}
{i : @El p Iᶠ} {iε : Elε Iᶠ Iε i} :
    side_0 · (homotopy_to_0ᶠ i iε) ≡ i0ᶠ.
Proof.
apply (@seq_I p (side_0 · homotopy_to_0ᶠ i iε) (side_0 · homotopy_to_0ε i iε) i0ᶠ i0ε).
apply seq_cube_arr. refine (srefl _).
Defined.

Definition restriction_1 {p : ℙ}
    {i : @El p Iᶠ} {iε : Elε Iᶠ Iε i} :
    side_1 · (homotopy_to_0ᶠ i iε) ≡ i.
Proof.
apply (@seq_I p (side_1 · homotopy_to_0ᶠ i iε) (side_1 · homotopy_to_0ε i iε) i iε).
apply seq_cube_arr. refine (srefl _).
Defined.

Definition ax1ᶠ {p : ℙ}
    (φ : @El p (Arr Iᶠ Iε Typeᶠ Typeε))
    (φε : Elε _ (Arrε Iᶠ Iε Typeᶠ Typeε) φ)
    (Hφ : @El p (Prod Iᶠ Iε (isdecᶠ φ φε) (isdecε φ φε)))
    (Hφε : Elε _ (Prodε Iᶠ Iε (isdecᶠ φ φε) (isdecε φ φε)) Hφ) :
    @El p (sumᶠ (Prod Iᶠ Iε φ φε) (Prodε Iᶠ Iε φ φε)
                (Prod Iᶠ Iε (negᶠ φ φε) (negε φ φε))
                (Prodε Iᶠ Iε (negᶠ φ φε) (negε φ φε))).
Proof.
unshelve refine (fun q α => _).
pose proof (Hφ q α (α · i0ᶠ) (α · i0ε)) as H. destruct H as [Hi0 Hi0ε | Hi0 Hi0ε].
- unshelve refine (inl_ _ _ _ _ _ _).
  + unshelve refine (fun r β i iε => _).
    (* pose proof (Hφ r (α ∘ β) (homotopy_to_0ᶠ i iε) (homotopy_to_0ε i iε)) as Hh. *)
Admitted.

(* Axiom 2 *)

Definition ax2ᶠ {p : ℙ}
    (e : @El p (eqᶠ Iᶠ Iε i0ᶠ i0ε i1ᶠ i1ε))
    (eε : Elε _ (eqε Iᶠ Iε i0ᶠ i0ε i1ᶠ i1ε) e) :
    @El p emptyᶠ.
Proof.
refine (fun q α => _).
pose proof (mkFinset 1 0 (sle_n _)) as z.
pose proof (fun _ : finset q => false) as c.
pose proof (match e q α in (eq_ _ _ _ _ x xε)
        return (((α · i0ᶠ) q !).(arr) c z = (x q !).(arr) c z) with
        | refl_ _ _ _ _ => eq_refl _
        end) as H.
inversion H.
Defined.

Definition ax2ε {p : ℙ}
    (e : @El p (eqᶠ Iᶠ Iε i0ᶠ i0ε i1ᶠ i1ε))
    (eε : Elε _ (eqε Iᶠ Iε i0ᶠ i0ε i1ᶠ i1ε) e) :
    Elε emptyᶠ emptyε (ax2ᶠ e eε).
Proof.
refine (fun q α => sI).
Defined.

(*Axiom 3 *)

Lemma increase_impliesb {q} (i : q ≤ 1) (x y : cube q) (H : le_cube x y) (n : finset 1) : (arr i x n) = true ->  (arr i y n) = true.
Proof.
  intro Hx.
  assert (Hi := eps_arr i x y H n).
  destruct (arr i x n).
  - destruct (arr i y n).
    + reflexivity.
    + destruct Hi.
  - discriminate.
Defined.

Definition mincube {p} (i j : cube_arr p 1) : cube_arr p 1.
Proof.
  unshelve econstructor.
  - intros x n. exact (andb (arr i x n) (arr j x n)).
  - intros x y H n.
    set (ixn := (arr i x n)). assert (arr i x n = ixn) by reflexivity. destruct ixn.
    + set (jxn := (arr j x n)). assert (arr j x n = jxn) by reflexivity. destruct jxn.
      * rewrite (increase_impliesb i x y H n H0).
        rewrite (increase_impliesb j x y H n H1).
        constructor.
      * constructor.
    + constructor.
Defined.

Definition minIᶠ {p} (i j : @El p Iᶠ) : @El p Iᶠ.
Proof.
  intros q α.
  assert (t := mincube (i p !) (j p !)).
  exact (t ∘ α).
Defined.

Definition minIε {p} {i j : @El p Iᶠ} (iε : Elε Iᶠ Iε i) (jε : Elε Iᶠ Iε j) : @Elε p Iᶠ Iε (minIᶠ i j).
Proof.
  intros q α.
  unfold cast. simpl.
  change (α · minIᶠ i j)
    with  (fun (r : nat) (β : r ≤ q) => mincube (i p !) (j p !) ∘ α ∘ β).
  constructor.
Defined.


(* Axiom 4 *)

Definition maxcube {p} (i j : cube_arr p 1) : cube_arr p 1.
Proof.
  unshelve econstructor.
  - intros x n. exact (orb (arr i x n) (arr j x n)).
  - intros x y H n.
    set (ixn := (arr i x n)). assert (arr i x n = ixn) by reflexivity. destruct ixn.
    + rewrite (increase_impliesb i x y H n H0).
      constructor.
    + set (jxn := (arr j x n)). assert (arr j x n = jxn) by reflexivity. destruct jxn.
      * rewrite (increase_impliesb j x y H n H1).
        simpl. destruct (arr i y n); constructor.
      * constructor.
Defined.

Definition maxIᶠ {p} (i j : @El p Iᶠ) : @El p Iᶠ.
Proof.
  intros q α.
  assert (t := maxcube (i p !) (j p !)).
  exact (t ∘ α).
Defined.

Definition maxIε {p} (i j : @El p Iᶠ)
           (iε : Elε Iᶠ Iε i) (jε : Elε Iᶠ Iε j) : @Elε p Iᶠ Iε (maxIᶠ i j).
Proof.
  intros q α.
  unfold cast. simpl.
  change (α · maxIᶠ i j)
    with  (fun (r : nat) (β : r ≤ q) => maxcube (i p !) (j p !) ∘ α ∘ β).
  constructor.
Defined.


