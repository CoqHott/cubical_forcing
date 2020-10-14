From Theories Require Import category.
From Theories Require Import translation_fib.
From Theories Require Import transport.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(* weak univalence *)
(* for now lets just try to glue bool along bool... *)

(* Definition glueType (p : ℙ) (A B : Type) : itype p Type A B.
Proof.
refine (J_seq _ (glueTypeAux p A B i0) (fun X _ => itype p Type X B) _ _ (glueTypeAux_i0)).
refine (J_seq _ (glueTypeAux p A B i1) (fun X _ => itype p Type (glueTypeAux p A B i0) X) _ _ (glueTypeAux_i1)).
refine (itype_in (glueTypeAux p A B)).
Defined.

Definition weakunivalence0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (B0 : @El0 p Type0)
  (B1 : @El1 p Type0 Type1 B0)
  : El0 (eq0 Type0 Type1 A0 A1 B0 B1).
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β => _).
  unshelve econstructor.
  + refine (fun r0 β0 => _).
    refine (itype_out (glueType r0 (yft0 (A0 r0 (α ∘ squish ∘ β ∘ β0)) r0 !) (yft0 (B0 r0 (α ∘ squish ∘ β ∘ β0)) r0 !)) (antisquish ∘ β ∘ β0)).
  + refine (fun r0 β0 s => _) ; simpl in s.
    admit.
  + refine (fun r0 β0 a b c d e => _).
    admit.
- refine (fun r β r0 β0 => _). unfold cast0 ; simpl. reflexivity.
- simpl.
Admitted. *)

Inductive bool' : Set :=
| true' : bool'
| false' : bool'.

Definition bool'R {p} : (forall q (α : q ≤ p), bool') -> SProp :=
fun s => s ≡ fun q α => s p !.

Definition bool'0 {p} : @El0 p Type0.
Proof.
unshelve refine (fun q α => mkYFT _ _ _ _).
- unshelve refine (fun r β => bool').
- unshelve refine (fun r β s => bool'R s).
- unshelve refine (fun r β b e l le l' => _).
  unshelve econstructor.
  + unfold yt_funct ; simpl.
    unshelve econstructor ; simpl.
    apply falso.
    apply sfalso.
  + apply sfalso.
Defined.

Definition bool'1 {p} : @El1 p Type0 Type1 bool'0.
Proof.
unshelve refine (fun q α => _).
reflexivity.
Defined.

Definition is_i1 {p} : p ≤ 1 -> bool.
Admitted.

Definition i1_is_i1 : (fun p => is_i1 (@i1 p)) ≡ fun _ => true.
Admitted.

Definition gluetest {p q} (α : q ≤ S p) :=
  if is_i1 (antisquish ∘ α) then bool' else bool.

Definition gluetest_funct {p q} {α : q ≤ S p} {r} (β : r ≤ q) :
  gluetest α -> gluetest (α ∘ β).
Admitted.

Definition glue_test0 {p} :
  @El0 (S p) (squish ⋅ Type0).
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β => _).
  refine (gluetest (α ∘ β)).
- refine (fun r β => _).
  refine (fun s => s ≡ (fun r0 β0 => gluetest_funct β0 (s r !))).
- unshelve refine (fun r β b e l le l' => _).
  apply falso.
Defined.

Record yt_seq {p} (a b : forall q (α : q ≤ p), yt q) : SProp :=
mkYTSEQ {
  ytseq0 : (fun q (α : q ≤ p) => yt0 (a q α)) ≡ (fun q (α : q ≤ p) => yt0 (b q α)) ;
  ytseq1 : (fun q (α : q ≤ p) r (β : r ≤ q) (s : forall r0 (β0 : r0 ≤ r), yt0 (b q α) r0 (β ∘ β0)) =>
      yt1 (a q α) r β
          (fun r0 (β0 : r0 ≤ r) => J_seq _ _ (fun X _ => X q α r0 (β ∘ β0)) (s r0 β0) _ (ssym ytseq0)))
    ≡ (fun q (α : q ≤ p) => yt1 (b q α)) ;
  }.

Lemma trans {A : Type} {a b c : A} (e1 : a ≡ b) (e2 : b ≡ c) : a ≡ c.
  Admitted.

Lemma yt_seq_to_seq {p} (a b : forall q (α : q ≤ p), yt q) :
  yt_seq a b -> a ≡ b.
Proof.
refine (fun Hab => _).
pose proof (ytseq0 _ _ Hab) as Hab0.
pose proof (ytseq1 _ _ Hab) as Hab1.
change ((fun q (α : q ≤ p) =>
  {| yt0 := yt0 (a q α) ;
     yt1 := fun r (β : r ≤ q) (s : forall r0 (β0 : r0 ≤ r), yt0 (a q α) r0 (β ∘ β0)) => yt1 (a q α) r β (fun r0 (β0 : r0 ≤ r) => s r0 β0) |})
≡
(fun q (α : q ≤ p) =>
  {| yt0 := yt0 (b q α) ;
     yt1 := yt1 (b q α) |})).
refine (J_seqs _ (fun q (α : q ≤ p) => yt0 (b q α))
  (fun X E =>
    (fun q (α : q ≤ p) => {|
      yt0 := X q α ;
      yt1 := fun r (β : r ≤ q) (s : forall r0 (β0 : r0 ≤ r), X q α r0 (β ∘ β0)) =>
        yt1 (a q α) r β
        (fun r0 (β0 : r0 ≤ r) => J_seq _ X (fun Y _ => Y q α r0 (β ∘ β0)) (s r0 β0) (fun q (α : q ≤ p) => yt0 (a q α)) (trans (ssym E) (ssym Hab0))) |})
  ≡ (fun q (α : q ≤ p) => {| yt0 := yt0 (b q α) ; yt1 := yt1 (b q α) |}))
  _ (fun q (α : q ≤ p) => yt0 (a q α)) (ssym Hab0)).
refine (J_seqs _ _ (fun X _ => (fun q (α : q ≤ p) =>
  {| yt0 := yt0 (b q α) ;
     yt1 := X q α |}) ≡ b) _ _ (ssym Hab1)).
reflexivity.
Defined.

Record yft_seq {p} (a b : forall q (α : q ≤ p), yft q) : SProp :=
mkYFTSEQ {
  yftseq0 : (fun q (α : q ≤ p) => yft0 (a q α)) ≡ (fun q (α : q ≤ p) => yft0 (b q α)) ;
  yftseq1 : (fun q (α : q ≤ p) r (β : r ≤ q) (s : forall r0 (β0 : r0 ≤ r), yft0 (b q α) r0 (β ∘ β0)) =>
      yft1 (a q α) r β
          (fun r0 (β0 : r0 ≤ r) => J_seq _ _ (fun X _ => X q α r0 (β ∘ β0)) (s r0 β0) _ (ssym yftseq0)))
    ≡ (fun q (α : q ≤ p) => yft1 (b q α)) ;
  }.

Goal ~ (~ (forall P : Prop, P \/ (~ P))).
intro s.

Lemma test {p} : 
  yft_seq (side_1 ⋅ (@glue_test0 p)) (bool'0).
Proof.
unshelve econstructor.
- change ((fun q (α : q ≤ p) r (β : r ≤ q) => if is_i1 (@i1 r) then bool' else bool) ≡ (fun q (α : q ≤ p) r (β : r ≤ q) => bool')).
  refine (J_seqs (nat -> bool) (fun _ => true) (fun X _ => (fun q (α : q ≤ p) r (β : r ≤ q) => if X r then bool' else bool) ≡ _) (srefl _) _ (ssym i1_is_i1)).
- simpl. unfold bool'R. 
  assert (let x := (fun y => y) bool in x) as H. admit.
  cbv zeta in H.
 (* assuming is_i1 (i1) reduces to true, that reduces to the following *)
 assert ((fun q (α : q ≤ p) r (β : r ≤ q) (s : forall r0 (β0 : r0 ≤ r), bool') =>
    s ≡ (fun r0 (β0 : r0 ≤ r) => gluetest_funct β0 (s r !)))
  ≡
  (fun q (α : q ≤ p) r (β : r ≤ q) (s : forall r0 (β0 : r0 ≤ r), bool') =>
    s ≡ (fun r0 (β0 : r0 ≤ r) => s r !))).



unshelve econstructor.
  + refine (fun r0 β0 => _).
    exact (if (is_i1 (antisquish ∘ β ∘ β0)) then bool' else bool).
  + refine (fun r0 β0 => _).
    admit.

    apply falso.
- refine (fun r β => _). unshelve
  (itype r0 Type bool bool').

Definition univ_test0 {p} :
  @El0 p (eq0 Type0 Type1 bool0 bool1 bool'0 bool'1).
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β => _).