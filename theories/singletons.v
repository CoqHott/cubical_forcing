From Theories Require Import category.
From Theories Require Import translation_fib.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

(* contractibility of singletons *)

Record wedge_eq {p} 
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0) : Type :=
mkWE {
  we_f0 : @El0 (S (S p)) (squish ∘ squish ⋅ A0) ;
  we_f1 : @El1 (S (S p)) (squish ∘ squish ⋅ A0) (squish ∘ squish ⋅ A1) we_f0 ;
  we_0y : side_0 ⋅ we_f0 ≡ squish ⋅ a0 ;
  we_1y : side_1 ⋅ we_f0 ≡ ce_f0 (e0 p !) ;
  we_x0 : promote side_0 ⋅ we_f0 ≡ squish ⋅ a0 ;
  we_x1 : promote side_1 ⋅ we_f0 ≡ ce_f0 (e0 p !) ;
}.

Arguments we_f0 {_ _ _ _ _ _ _ _ _}.
Arguments we_f1 {_ _ _ _ _ _ _ _ _}.
Arguments we_0y {_ _ _ _ _ _ _ _ _}.
Arguments we_1y {_ _ _ _ _ _ _ _ _}.
Arguments we_x0 {_ _ _ _ _ _ _ _ _}.
Arguments we_x1 {_ _ _ _ _ _ _ _ _}.

Definition we_funct {p} 
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0) {q} (α : q ≤ p) :
  wedge_eq A0 A1 a0 a1 b0 b1 e0 e1 -> wedge_eq (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1).
Proof.
unshelve refine (fun x => _).
unshelve econstructor.
- exact (promote (promote α) ⋅ x.(we_f0)).
- exact (promote (promote α) ⋅ x.(we_f1)).
- refine (J_seqs _ _ (fun X _ => promote α ⋅ X ≡ _) (srefl _) _ (ssym (we_0y x))).
- refine (J_seqs _ _ (fun X _ => promote α ⋅ X ≡ _) _ _ (ssym (we_1y x))).
  refine (J_seqs _ (fun q α => ce_funct α (e0 p !)) (fun X _ => _ ≡ ce_f0 (X q α)) (srefl _) _ (ssym (e1 p !))).
- refine (J_seqs _ _ (fun X _ => promote α ⋅ X ≡ _) (srefl _) _ (ssym (we_x0 x))).
- refine (J_seqs _ _ (fun X _ => promote α ⋅ X ≡ _) _ _ (ssym (we_x1 x))).
  refine (J_seqs _ (fun q α => ce_funct α (e0 p !)) (fun X _ => _ ≡ ce_f0 (X q α)) (srefl _) _ (ssym (e1 p !))).
Defined.

Definition wedge_eqR {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0) :
 (forall q (α : q ≤ p), wedge_eq (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) (α ⋅ b0) (α ⋅ b1) (α ⋅ e0) (α ⋅ e1)) -> SProp :=
fun s => s ≡ fun q α => we_funct A0 A1 a0 a1 b0 b1 e0 e1 α (s p !).

Definition contractor0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0)
  : @El0 p Type0.
Proof.
refine (fun q α => _). unshelve econstructor.
- unshelve refine (fun r β => _).
  exact (wedge_eq ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · a0) ((α ∘ β) · a1) ((α ∘ β) · b0) ((α ∘ β) · b1) ((α ∘ β) · e0) ((α ∘ β) · e1)).
- unshelve refine (fun r β s => _). simpl in s.
  exact (wedge_eqR ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · a0) ((α ∘ β) · a1) ((α ∘ β) · b0) ((α ∘ β) · b1) ((α ∘ β) · e0) ((α ∘ β) · e1) s).
- refine (fun r β c s0 s1 => _). apply falso.
- refine (fun r β c s0 s1 => _). apply falso.
- refine (fun r β c s0 s1 => _). apply sfalso.
- refine (fun r β c s0 s1 => _). apply sfalso.
Defined.

Definition contractor1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0)
  : @El1 p Type0 Type1 (contractor0 A0 A1 a0 a1 b0 b1 e0 e1).
Proof.
refine (fun q α r β => _).
reflexivity.
Defined.

Definition contr_filler0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0)
  : El0 (contractor0 A0 A1 a0 a1 b0 b1 e0 e1).
Proof.
refine (fun q α => _). simpl. unshelve econstructor.
- refine (wedge ⋅ ce_f0 (e0 q α)).
- refine (wedge ⋅ ce_f1 (e0 q α)).
- apply sfalso.
- apply sfalso.
- apply sfalso.
- apply sfalso.
(* as is, this requires some computation rules for wedge *)
Defined.

Definition contr_filler1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0)
  : El1 _ (contractor1 A0 A1 a0 a1 b0 b1 e0 e1) (contr_filler0 A0 A1 a0 a1 b0 b1 e0 e1).
Proof.
refine (fun q α => _).
assert (forall (f g : forall (r : ℙ) (β : r ≤ q), wedge_eq ((α ∘ β) · A0) ((α ∘ β) · A1) ((α ∘ β) · a0) ((α ∘ β) · a1) ((α ∘ β) · b0) ((α ∘ β) · b1) ((α ∘ β) · e0) ((α ∘ β) · e1)), 
  ((fun r β => we_f0 (f r β)) ≡ (fun r β => we_f0 (g r β))) -> f ≡ g)
  as lemma.
{ intros f g Hfg.
  refine (J_seqs _ (fun r β => we_f0 (g r β)) 
    (fun X E => (fun r β => 
      {| we_f0 := X r β ; 
         we_f1 := J_seqs _ _ (fun Y _ => El1 (squish ∘ squish ⋅ (α ∘ β ⋅ A0)) (squish ∘ squish ⋅ (α ∘ β ⋅ A1)) (Y r β)) (we_f1 (g r β)) _ E ;
         we_0y := J_seqs _ (fun r β => we_f0 (g r β)) (fun Y _ => side_0 ⋅ (Y r β) ≡ squish ⋅ (α ∘ β ⋅ a0)) (we_0y (g r β)) X E ; 
         we_1y := J_seqs _ _ (fun Y _ => side_1 ⋅ (Y r β) ≡ ce_f0 (e0 r (α ∘ β))) (we_1y (g r β)) X E ;
         we_x0 := J_seqs _ _ (fun Y _ => (promote side_0) ⋅ (Y r β) ≡ squish ⋅ (α ∘ β ⋅ a0)) (we_x0 (g r β)) X E ;
         we_x1 := J_seqs _ _ (fun Y _ => (promote side_1) ⋅ (Y r β) ≡ ce_f0 (e0 r (α ∘ β))) (we_x1 (g r β)) X E ; |}) 
      ≡ g)
    (srefl _)
    (fun r β => we_f0 (f r β))
    (ssym Hfg)). }
eapply lemma. simpl.
refine (J_seqs _ _ (fun X _ => (fun r β => wedge ⋅ ce_f0 (X r β)) ≡ _) (srefl _) (α ⋅ e0) (ssym (e1 q α))).
Defined.


(* that one is more or less contr_filler0 with some packaging *)
(* todo : prove it from contr_filler0 *)
Definition singl_contr0 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0)
  : El0 (eq0
    (Sigma0 A0 A1 (fun q α x0 x1 => eq0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !))
    (Sigma1 A0 A1 (fun q α x0 x1 => eq0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !))
    (dpair0 a0 a1 (eq_refl0 A0 A1 a0 a1) (eq_refl1 A0 A1 a0 a1))
    (dpair1 a0 a1 (eq_refl0 A0 A1 a0 a1) (eq_refl1 A0 A1 a0 a1))
    (dpair0 b0 b1 e0 e1)
    (dpair1 b0 b1 e0 e1)).
Proof.
refine (fun q α => _) ; simpl.
unshelve econstructor.
- refine (fun r β => _) ; simpl.
  unshelve econstructor.
  + exact (β ⋅ ce_f0 (e0 q α)).
  + exact (β ⋅ ce_f1 (e0 q α)).
  + refine (fun r0 β0 => _) ; simpl.
    unshelve econstructor.
    * change (El0 (α ∘ squish ∘ wedge ∘ promote β ∘ promote β0 ⋅ A0)).
      exact (wedge ∘ promote β ∘ promote β0 ⋅ (ce_f0 (e0 q α))).
    * exact (wedge ∘ promote β ∘ promote β0 ⋅ (ce_f1 (e0 q α))).
    * refine (J_seqs _ _ (fun X _ => _ ≡ β ∘ β0 ⋅ (squish ⋅ X)) _ _ (ce_s (e0 q α))).
      change (β ∘ β0 ⋅ (wedge ∘ side_0 ⋅ ce_f0 (e0 q α)) ≡ β ∘ β0 ⋅ (side_0 ∘ squish ⋅ (ce_f0 (e0 q α)))).
      (* here we would need some more computation *)
      apply sfalso.
    * change (β ∘ β0 ⋅ (wedge ∘ side_1 ⋅ ce_f0 (e0 q α)) ≡ β ∘ β0 ⋅ (ce_f0 (e0 q α))).
      (* here too *)
      apply sfalso.
  + refine (fun r0 β0 => _) ; simpl.
    reflexivity.
- refine (fun r β => _) ; simpl.
  reflexivity.
- admit.
- admit.
Admitted.


Definition singl_contr1 {p}
  (A0 : @El0 p Type0)
  (A1 : @El1 p Type0 Type1 A0)
  (a0 : El0 A0)
  (a1 : El1 A0 A1 a0)
  (b0 : El0 A0)
  (b1 : El1 A0 A1 b0)
  (e0 : El0 (eq0 A0 A1 a0 a1 b0 b1))
  (e1 : El1 _ (eq1 A0 A1 a0 a1 b0 b1) e0)
  : El1 _ (eq1
    (Sigma0 A0 A1 (fun q α x0 x1 => eq0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !))
    (Sigma1 A0 A1 (fun q α x0 x1 => eq0 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !) (fun q α x0 x1 => eq1 (α ⋅ A0) (α ⋅ A1) (α ⋅ a0) (α ⋅ a1) x0 x1 q !))
    (dpair0 a0 a1 (eq_refl0 A0 A1 a0 a1) (eq_refl1 A0 A1 a0 a1))
    (dpair1 a0 a1 (eq_refl0 A0 A1 a0 a1) (eq_refl1 A0 A1 a0 a1))
    (dpair0 b0 b1 e0 e1)
    (dpair1 b0 b1 e0 e1))
    (singl_contr0 A0 A1 a0 a1 b0 b1 e0 e1).
Proof.
refine (fun q α => _). simpl.
(* komarimasu… *)
Admitted.
