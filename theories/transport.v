From Theories Require Import category.
From Theories Require Import translation_fib.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(* shifted types *)

Record shifted_ty {p} : Type :=
mkST {
  st_t0 : @El0 (S p) (squish ⋅ Type0) ;
  st_t1 : @El1 (S p) (squish ⋅ Type0) (squish ⋅ Type1) st_t0 ;
}.

Definition st_funct {p} {q} (α : q ≤ p) :
  @shifted_ty p -> @shifted_ty q.
Proof.
unshelve refine (fun x => _).
unshelve econstructor.
- exact (promote α ⋅ x.(st_t0)).
- exact (promote α ⋅ x.(st_t1)).
Defined.

Definition shifted_tyR {p} :
 (forall q (α : q ≤ p), @shifted_ty q) -> SProp :=
fun s => s ≡ fun q α => st_funct α (s p !).

Definition shiftedType0 {p}
  : @El0 p Type0.
Proof.
unshelve econstructor.
- unshelve refine (fun r β => _).
  exact (@shifted_ty r).
- unshelve refine (fun r β s => _). simpl in s.
  exact (shifted_tyR s).
- refine (fun r β s0 s1 => _). apply falso.
- refine (fun r β s0 s1 => _). apply falso.
- refine (fun r β s0 s1 => _). apply sfalso.
- refine (fun r β s0 s1 => _). apply sfalso.
Defined.

Definition shiftedType1 {p}
  : @El1 p Type0 Type1 shiftedType0.
Proof.
refine (fun q α => _). reflexivity.
Defined.

Definition shiftedTypeStart0 {p}
  (A0 : @El0 p shiftedType0)
  (A1 : @El1 p shiftedType0 shiftedType1 A0) :
  @El0 p Type0.
Proof.
refine (fun q α => _).
refine ((side_0 ⋅ st_t0 (A0 q α)) q !). 
Defined.

Definition shiftedTypeStart1 {p}
  (A0 : @El0 p shiftedType0)
  (A1 : @El1 p shiftedType0 shiftedType1 A0) :
  @El1 p Type0 Type1 (shiftedTypeStart0 A0 A1).
Proof.
refine (fun q α => _). 
refine (J_seqs _ _ (fun X _ => yftR (fun r β => st_t0 (X r β) r side_0 )) _ (α ⋅ A0) (ssym (A1 q α))).
refine ((side_0 ⋅ st_t1 (A0 q α)) q !).
Defined.

Definition shiftedTypeEnd0 {p}
  (A0 : @El0 p shiftedType0)
  (A1 : @El1 p shiftedType0 shiftedType1 A0) :
  @El0 p Type0.
Proof.
refine (fun q α => _).
refine ((side_1 ⋅ st_t0 (A0 q α)) q !). 
Defined.

Definition shiftedTypeEnd1 {p}
  (A0 : @El0 p shiftedType0)
  (A1 : @El1 p shiftedType0 shiftedType1 A0) :
  @El1 p Type0 Type1 (shiftedTypeEnd0 A0 A1).
Proof.
refine (fun q α => _). 
refine (J_seqs _ _ (fun X _ => yftR (fun r β => st_t0 (X r β) r side_1)) _ (α ⋅ A0) (ssym (A1 q α))).
refine ((side_1 ⋅ st_t1 (A0 q α)) q !).
Defined.

(* a predicate over an equality is a shifted type *)

Definition eqToShiftedType0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0) :
  @El0 p shiftedType0.
Proof.
refine (fun q α => _).
unshelve econstructor.
- refine (fun r β => P0 r (α ∘ squish ∘ β) (β ⋅ (ce_f0 (e0 q α))) (β ⋅ ce_f1 (e0 q α))).
- refine (@app1 (S q) _ _ Type0 Type1 (α ∘ squish ⋅ P0) (α ∘ squish ⋅ P1) (ce_f0 (e0 q α)) (ce_f1 (e0 q α))).
Defined.

Definition eqToShiftedType1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0) :
  @El1 p shiftedType0 shiftedType1 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1).
Proof.
refine (fun q α => _).
unfold cast0 ; simpl. unfold shifted_tyR ; simpl.
change (eqToShiftedType0 (α ⋅ A0) (α ⋅ A1) (α ⋅ P0) (α ⋅ P1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1) ≡ (fun r β => st_funct β (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1 q α))).
pose proof (e1 q α) as He. unfold cast0 in He ; simpl in He.
unfold cube_eqR in He.
refine (J_seqs _ _ 
  (fun X e => eqToShiftedType0 _ _ _ _ _ _ _ _ X 
    (J_seqs _ _ (fun Y _ => El1 _ (eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1)) Y) 
      (J_seqs _ (α ⋅ e0) (fun Z _ => El1 _ (eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1)) Z) (α ⋅ e1) _ He) 
      X e) 
    ≡ _) 
  _ (α ⋅ e0) (ssym He)).
reflexivity.
Defined.

(* transport boils down to a statement about shifted types *)

Definition transp0 {p}
  (A0 : @El0 p shiftedType0)
  (A1 : @El1 p shiftedType0 shiftedType1 A0)
  (s0 : El0 (shiftedTypeStart0 A0 A1))
  (s1 : El1 _ (shiftedTypeStart1 A0 A1) s0)
  : El0 (shiftedTypeEnd0 A0 A1).
Proof.
refine (fun q α => _).
unfold shiftedTypeEnd0 ; simpl.
refine (J_seq _ _ (fun X _ => yft0 (X q side_1) q !) _ _ (ssym (st_t1 (A0 q α) (S q) !))).
change (yft0 (st_t0 (A0 q α) (S q) !) q side_1).

pose proof (yftfibl0 (st_t0 (A0 q α) (S q) !) q !) as fib0.
unshelve refine (fib0 _ _).
- refine (fun r β => _).
  refine (J_seq _ _ (fun X _ => yft0 (X r (side_0 ∘ β)) r !) _ _ (st_t1 (A0 q α) (S q) !)).
  refine (J_seq _ _ (fun X _ => yft0 (st_t0 (X r β) r side_0) r !) _ _ (A1 q α)).
  refine (s0 r (α ∘ β)).
- refine (fun r β => _).
  apply sfalso.
Defined.

Definition transp1 {p}
  (A0 : @El0 p shiftedType0)
  (A1 : @El1 p shiftedType0 shiftedType1 A0)
  (s0 : El0 (shiftedTypeStart0 A0 A1))
  (s1 : El1 _ (shiftedTypeStart1 A0 A1) s0)
  : El1 _ (shiftedTypeEnd1 A0 A1) (transp0 A0 A1 s0 s1).
Proof.
refine (fun q α => _).
unfold shiftedTypeEnd0 ; simpl.
unfold transp0 ; simpl.
unfold cast0 ; simpl.
Admitted.

Definition transport_aux1_0 {p}
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
  El0 (shiftedTypeStart0 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)).
Proof.
refine (fun q α => _).
change (yft0 (P0 q α (side_0 ⋅ ce_f0 (e0 q α)) (side_0 ⋅ ce_f1 (e0 q α))) q !).
refine (J_seq _ (α ⋅ a0) 
  (fun X E => yft0 (P0 q α X 
    (J_seqs _ _ (fun Y _ => El1 (α ⋅ A0) (α ⋅ A1) Y) (α ⋅ a1) X E)) 
    q !)
  _ _ (ssym (ce_s (e0 q α)))).
refine (x0 q α).
Defined.

Definition transport_aux1_1 {p}
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
  El1 _ (shiftedTypeStart1 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)) (transport_aux1_0 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1).
Proof.
refine (fun q α => _). 
unfold transport_aux1_0 ; simpl.
unfold shiftedTypeStart0 ; unfold eqToShiftedType0 at 1 2 ; simpl.
(* unfolding shiftedTypeStart1 unleashes hell *)
Admitted.

Definition transport_aux2_0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0)
  (x0 : El0 (shiftedTypeEnd0 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)))
  (x1 : El1 _ (shiftedTypeEnd1 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)) x0) :
  El0 (app0 P0 b0 b1).
Proof.
refine (fun q α => _).
change (yft0 (P0 q α (α ⋅ b0) (α ⋅ b1)) q !).
refine (J_seq _ _ 
  (fun X E => yft0 (P0 q α X 
    (J_seqs _ _ (fun Y _ => El1 (α ⋅ A0) (α ⋅ A1) Y) 
      (J_seqs _ (α ⋅ b0) (fun Z _ => El1 (α ⋅ A0) (α ⋅ A1) Z) (α ⋅ b1) _ (ssym (ce_t (e0 q α)))) X E)) 
    q !)
  _ (α ⋅ b0) (ce_t (e0 q α))).
change (yft0 (P0 q α (side_1 ⋅ ce_f0 (e0 q α)) (side_1 ⋅ ce_f1 (e0 q α))) q !).
refine (x0 q α).
Defined.

Definition transport_aux2_1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (P0 : El0 (Arr0 A0 A1 Type0 Type1))
  (P1 : El1 _ (Arr1 A0 A1 Type0 Type1) P0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0)
  (x0 : El0 (shiftedTypeEnd0 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)))
  (x1 : El1 _ (shiftedTypeEnd1 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)) x0) :
  El1 (app0 P0 b0 b1) (app1 P1 b0 b1) (transport_aux2_0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1 x0 x1).
Proof.
Admitted.

Definition transport0 {p}
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
refine (transport_aux2_0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1 
  (transp0 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)
    (transport_aux1_0 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1)
    (transport_aux1_1 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1))
  (transp1 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)
    (transport_aux1_0 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1)
    (transport_aux1_1 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1))).
Defined.

Definition transport1 {p}
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
  El1 (app0 P0 b0 b1) (app1 P1 b0 b1) (transport0 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1).
Proof.
refine (transport_aux2_1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1 
  (transp0 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)
    (transport_aux1_0 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1)
    (transport_aux1_1 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1))
  (transp1 (eqToShiftedType0 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1) (eqToShiftedType1 A0 A1 P0 P1 a0 a1 b0 b1 e0 e1)
    (transport_aux1_0 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1)
    (transport_aux1_1 A0 A1 P0 P1 a0 a1 x0 x1 b0 b1 e0 e1))).
Defined.
