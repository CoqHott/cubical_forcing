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

