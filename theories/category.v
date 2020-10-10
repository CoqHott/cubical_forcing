Require Import Arith.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Inductive seq {A : Type} (x : A) : A -> SProp := srefl : seq x x.

Notation "x ≡ y" := (seq x y) (at level 70).

(*
Axiom J_seq : forall (A : Type) (x : A) (P : forall y, x ≡ y -> Type),
  P x (srefl _) -> forall y e, P y e.
*)
Lemma J_seq : forall (A : Type) (x : A) (P : forall y, x ≡ y -> Type),
  P x (srefl _) -> forall y e, P y e.
Proof.
intros A x P p y e.
refine (match e in _ ≡ z as e return P _ e with srefl _ => p end).
Defined.

Lemma transp_seq {A : Type} {x : A} (P : A -> Type)
  (a : P x) {y : A} (e : x ≡ y) : P y.
Proof.
refine (match e in _ ≡ z as e return P _ with srefl _ => a end).
Defined.

Lemma J_seqs : forall (A : Type) (x : A) (P : forall y, x ≡ y -> SProp),
  P x (srefl _) -> forall y e, P y e.
Proof.
intros A x P p y e.
refine (match e in _ ≡ z as e return P _ e with srefl _ => p end).
Defined.

Lemma transp_seqs {A : Type} {x : A} (P : A -> SProp)
  (a : P x) {y : A} (e : x ≡ y) : P y.
Proof.
refine (match e in _ ≡ z as e return P _ with srefl _ => a end).
Defined.

Definition ssym {A} {x y : A} (e : x ≡ y) : (y ≡ x).
Proof.
  destruct e. exact (srefl _).
Defined.

Inductive sFalse : SProp :=.
Inductive sTrue : SProp := sI.


(* Proof-irrelevant inequalities *)

Inductive sle (n : nat) : nat -> SProp :=
| sle_n : sle n n
| sle_S : forall m : nat, sle n m -> sle n (S m).

Definition le_to_sle {m n : nat} :
  le m n -> sle m n.
Proof.
intro H. induction H as [| m' n' IH].
- exact (sle_n m).
- exact (sle_S m m' IH).
Defined.

Definition sle_to_le {m n : nat} :
  sle m n -> le m n.
Proof.
intro H.
destruct (dec_le m n) as [Hd | Hd].
- exact Hd.
- assert (sFalse) as Hf.
  { induction H as [| m' n' IHsle].
    - destruct (Hd (le_n m)).
    - apply IHsle. intro H'. exact (Hd (le_S m m' H')). }
  destruct Hf.
Defined.

Definition slt (n m : nat) : SProp := sle (S n) m.

(* Finite sets *)

Record finset (n : nat) : Set := mkFinset {
    val : nat ;
    eps_val : slt val n ;
}.

Definition finzero {p : nat} : finset (S p).
Proof.
unshelve refine (mkFinset _ _ _).
+ exact 0.
+ apply le_to_sle. apply le_n_S. exact (le_0_n p).
Defined.

Definition finsucc {p : nat} (n : finset p) : finset (S p).
Proof.
destruct n as [n nε].
unshelve refine (mkFinset _ _ _).
+ exact (S n).
+ apply le_to_sle. apply le_n_S. apply sle_to_le. exact nε.
Defined.

Definition finmatch {m : nat} (P : finset (S m) -> Type)
  (P0 : P finzero) (PS : forall n, P (finsucc n)) : forall n, P n.
Proof.
refine (fun n => _). destruct n as [v ε]. revert ε.
destruct v.
- refine (fun ε => P0).
- refine (fun ε => PS {| val := v ; eps_val := le_to_sle (le_S_n _ _ (sle_to_le ε)) |}).
Defined.

Definition sfinmatch {m : nat} (P : finset (S m) -> SProp)
  (P0 : P finzero) (PS : forall n, P (finsucc n)) : forall n, P n.
Proof.
refine (fun n => _). destruct n as [v ε]. revert ε.
destruct v.
- refine (fun ε => P0).
- refine (fun ε => PS {| val := v ; eps_val := le_to_sle (le_S_n _ _ (sle_to_le ε)) |}).
Defined.

Arguments val {_}.
Arguments eps_val {_}.

(* Arrows *)

Definition cube (n : nat) : Set := finset n -> bool.

Definition le_cube {n : nat} (p q : cube n) : SProp :=
  forall m : finset n, if p m then (if q m then sTrue else sFalse) else sTrue. 

Definition increasing {m n : nat} (f : cube m -> cube n) : SProp :=
  forall x y : cube m, le_cube x y -> le_cube (f x) (f y).

Record cube_arr (m n : nat) : Set := mkCubeArr {
    arr : cube m -> cube n ;
    eps_arr : increasing arr ;
}.

Arguments arr {_ _}.
Arguments eps_arr {_ _}.

Definition seq_cube_arr {p q : nat} {α β : cube_arr p q} :
    α.(arr) ≡ β.(arr) -> α ≡ β.
Proof.
intro H.
destruct α as [α αε]. destruct β as [β βε].
simpl in H. destruct H. refine (srefl _).
Defined.

(* Composition *)

Definition comp_increasing {m n n' : nat} {f : cube m -> cube n} {g : cube n -> cube n'} :
  increasing f -> increasing g -> increasing (fun x => g (f x)).
Proof.
unshelve refine (fun Hf Hg x y Hxy => _).
unshelve refine (Hg (f x) (f y) _).
unshelve refine (Hf x y Hxy).
Defined.

Definition comp {m n n' : nat} (f : cube_arr m n) (g : cube_arr n n') : cube_arr m n'.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
+ unshelve refine (fun x => g.(arr) (f.(arr) x)).
+ unshelve refine (comp_increasing f.(eps_arr) g.(eps_arr)).
Defined.


(* Identity *)

Definition id_cube (n : nat) : cube_arr n n.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
+ unshelve refine (fun x => x).
+ unshelve refine (fun x y Hxy => Hxy).
Defined. 


(* Definitional category *)
(* equations hold by reflexivity *)

Lemma comp_assoc (m m' n n' : nat) (f : cube_arr m m') (g : cube_arr m' n) (h : cube_arr n n') :
  comp (comp f g) h = comp f (comp g h).
Proof.
reflexivity.
Qed.

Lemma comp_id_left (m n : nat) (f : cube_arr m n) :
  comp f (id_cube n) = f.
Proof.
reflexivity.
Qed.

Lemma comp_id_right (m n : nat) (f : cube_arr m n) :
  comp (id_cube m) f = f.
Proof.
reflexivity.
Qed.

(* Notations *)

Definition ℙ@{} : Set := nat.

Definition le@{} p q := cube_arr p q.

Definition le_id {p} : le p p := id_cube p.
Definition le_cmp {p q r} (α : le p q) (β : le q r) : le p r := comp α β.

Notation "p ≤ q" := (le p q) (at level 70, no associativity).
Notation "'!'" := (@le_id _).
Notation "α ∘ β" := (@le_cmp _ _ _ β α) (at level 35).

Notation "α · x" := (fun r β => x r (α ∘ β)) (at level 40).

(* useful arrows *)

Definition side_0 {p : ℙ} : p ≤ S p.
Proof.
unshelve econstructor.
- unshelve refine (fun c => _).
  refine (finmatch (fun _ => bool) _ _).
  + exact false.
  + refine (fun n => c n).
- intros c d Hcd.
  refine (sfinmatch _ _ _) ; simpl.
  + exact sI.
  + refine (fun n => _). refine (Hcd _).
Defined.

Definition side_1 {p : ℙ} : p ≤ S p.
Proof.
unshelve econstructor.
- unshelve refine (fun c => _).
  refine (finmatch (fun _ => bool) _ _).
  + exact true.
  + refine (fun n => c n).
- intros c d Hcd.
  refine (sfinmatch _ _ _) ; simpl.
  + exact sI.
  + refine (fun n => _). refine (Hcd _).
Defined.

Definition squish {p : ℙ} : S p ≤ p.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
- refine (fun c n => c (finsucc n)).
- intros c d Hcd n.
  exact (Hcd (finsucc n)).
Defined.

Definition antisquish {p : ℙ} : S p ≤ 1.
Proof.
unshelve econstructor.
- refine (fun c n => c finzero).
- intros c d Hcd n.
  exact (Hcd finzero).
Defined.

Definition promote {p q : ℙ} (α : q ≤ p) : S q ≤ S p.
Proof.
unshelve refine (mkCubeArr _ _ _ _).
- unshelve refine (fun c => _).
  refine (finmatch (fun _ => bool) _ _).
  + exact (c finzero).
  + apply (arr α).
    refine (fun n => c (finsucc n)).
- intros c d Hcd.
  refine (sfinmatch _ _ _) ; simpl.
  + eapply Hcd.
  + eapply (eps_arr α). 
    refine (fun m => _). eapply Hcd.
Defined.

Definition merge {p q : ℙ} (α : q ≤ p) (β : q ≤ 1) : q ≤ S p.
Proof.
unshelve econstructor.
- refine (fun c => _). 
  refine (finmatch (fun _ => bool) _ _).
  + refine (β.(arr) c finzero).
  + refine (fun n => α.(arr) c n).
- intros c d Hcd.
  refine (sfinmatch _ _ _) ; simpl.
  + exact (β.(eps_arr) c d Hcd finzero).
  + refine (fun n => α.(eps_arr) c d Hcd n).
Defined.

Definition vee {p : ℙ} : S (S p) ≤ S p.
Proof.
unshelve econstructor.
- refine (fun c => _).
  refine (finmatch (fun _ => bool) _ _).
  + exact (orb (c finzero) (c (finsucc finzero))).
  + refine (fun n' => _).
    exact (c (finsucc (finsucc n'))).
- intros c d Hcd.
  refine (sfinmatch _ _ _) ; simpl.
  + pose proof (Hcd finzero) as H0. pose proof (Hcd (finsucc finzero)) as H1.
    revert H0 H1. destruct (c finzero) ; destruct (c (finsucc finzero)) ; destruct (d finzero) ; destruct (d (finsucc finzero)) ; simpl ; easy.
  + refine (fun n => _). eapply Hcd.
Defined.

Definition wedge {p : ℙ} : S (S p) ≤ S p.
Proof.
unshelve econstructor.
- refine (fun c => _).
  refine (finmatch (fun _ => bool) _ _).
  + exact (andb (c finzero) (c (finsucc finzero))).
  + refine (fun n' => _).
    exact (c (finsucc (finsucc n'))).
- intros c d Hcd.
  refine (sfinmatch _ _ _) ; simpl.
  + pose proof (Hcd finzero) as H0. pose proof (Hcd (finsucc finzero)) as H1.
    revert H0 H1. destruct (c finzero) ; destruct (c (finsucc finzero)) ; destruct (d finzero) ; destruct (d (finsucc finzero)) ; simpl ; easy.
  + refine (fun n => _). eapply Hcd.
Defined.

(* All of the following hold definitionally *)

Lemma arrow_eq_0 {p : ℙ} : (@squish p) ∘ side_0 = !.
Proof.
reflexivity.
Defined.

Lemma arrow_eq_1 {p : ℙ} : (@squish p) ∘ side_1 = !.
Proof.
reflexivity.
Defined.

Lemma arrow_eq_2 {p q : ℙ} (α : q ≤ p) :
  promote α ∘ side_0 = side_0 ∘ α.
Proof.
reflexivity.
Defined.

Lemma arrow_eq_3 {p q : ℙ} (α : q ≤ p) :
  promote α ∘ side_1 = side_1 ∘ α.
Proof.
reflexivity.
Defined.

Lemma arrow_eq_4 {p q : ℙ} (α : q ≤ p) :
  squish ∘ promote α = α ∘ squish.
Proof.
reflexivity.
Defined.

Lemma arrow_eq_5 {p q : ℙ} (α : q ≤ p) (β : q ≤ 1) : 
  squish ∘ (merge α β) ≡ α.
Proof.
reflexivity.
Defined.

Lemma arrow_eq_6 {p q r : ℙ} (α : q ≤ p) (β : q ≤ 1) (γ : r ≤ q) : 
  (merge α β) ∘ γ ≡ merge (α ∘ γ) (β ∘ γ).
Proof.
reflexivity.
Defined.

Lemma arrow_eq_7 {p : ℙ} : squish ∘ squish ≡ squish ∘ (@wedge p).
Proof.
reflexivity.
Defined.

Lemma arrow_eq_8 {p : ℙ} : squish ∘ squish ≡ squish ∘ (@vee p).
Proof.
reflexivity.
Defined.

(* these ones, however, requires η for nat. 
  without it, we can only get an extensional equality. tough luck *)

Lemma arrow_eq_fail1 {p q : ℙ} (α : q ≤ S p) : 
  forall c n, (merge (squish ∘ α) (antisquish ∘ α)).(arr) c n ≡ α.(arr) c n.
Proof.
refine (fun c n => _). revert n.
refine (sfinmatch _ _ _) ; reflexivity.
Defined.

Lemma arrow_eq_fail2 {p : ℙ} : 
  forall c n, (wedge ∘ (@side_1 (S p))).(arr) c n ≡ !.(arr) c n.
Proof.
refine (fun c n => _). revert n.
refine (sfinmatch _ _ _) ; reflexivity.
Defined.

Lemma arrow_eq_fail3 {p : ℙ} : 
  forall c n, (wedge ∘ (@side_0 (S p))).(arr) c n ≡ (side_0 ∘ squish).(arr) c n.
Proof.
refine (fun c n => _). revert n.
refine (sfinmatch _ _ _) ; reflexivity.
Defined.

Lemma arrow_eq_fail4 {p : ℙ} : 
  forall c n, (wedge ∘ (promote (@side_1 p))).(arr) c n ≡ !.(arr) c n.
Proof.
refine (fun c n => _). revert n.
refine (sfinmatch _ _ _).
- unfold vee ; unfold promote ; unfold side_1 ; simpl. 
  destruct (c finzero) ; easy.
- easy.
Defined.

Lemma arrow_eq_fail5 {p : ℙ} : 
  forall c n, (wedge ∘ (promote (@side_0 p))).(arr) c n ≡ (side_0 ∘ squish).(arr) c n.
Proof.
refine (fun c n => _). revert n.
refine (sfinmatch _ _ _).
- unfold vee ; unfold promote ; unfold side_0 ; simpl. 
  destruct (c finzero) ; easy.
- easy.
Defined.

(* Axioms for interval-types, à la CubicalTT *)

Definition i0 {p} : p ≤ 1.
Proof.
unshelve econstructor.
- refine (fun c n => false).
- refine (fun c d Hcd n => _). easy.
Defined.

Definition i1 {p} : p ≤ 1.
Proof.
unshelve econstructor.
- refine (fun c n => true).
- refine (fun c d Hcd n => _). easy.
Defined.

Definition itype (p : ℙ) (A : Type) (x y : A) : Type.
Admitted.

Definition itype_in {p} {A : Type} (z : p ≤ 1 -> A) :
  itype p A (z i0) (z i1).
Admitted.

Definition itype_out {p} {A : Type} {x y : A} :
  itype p A x y -> p ≤ 1 -> A.
Admitted.

Definition itype_inout :
  (fun p A (x : p ≤ 1 -> A) y => itype_out (itype_in x) y) ≡ fun p A x y => x y.
Admitted.

Definition itype_out0 :
  (fun p (X : Type) (y z : X) (x : itype p X y z) => itype_out x i0) ≡ (fun p X y z x => y).
Admitted.

Definition itype_out1 :
  (fun p (X : Type) (y z : X) (x : itype p X y z) => itype_out x i1) ≡ (fun p X y z x => z).
Admitted.

