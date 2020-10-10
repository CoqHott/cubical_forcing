From Theories Require Import category.
From Theories Require Import translation_fib.

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

