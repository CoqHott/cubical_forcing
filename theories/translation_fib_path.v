From Theories Require Import category.
From Theories Require Import translation_fib.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.


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

(* comparing eq and path *)
(* we get functions both ways, but they do not form an equivalence without funext/η, since
   α ≠ merge (squish ∘ α) (antisquish ∘ α) *)

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
  eapply itype_out0_3.
- change ((fun r β => itype_out (e0 r (α ∘ β)) (side1)) ≡ α ⋅ y0).
  eapply itype_out1_3.
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
refine (J_seq _ _ (fun x _ => itype q _ (x q !) _) _ _ ((e0 q α).(ce_s))).
refine (J_seq _ _ (fun x _ => itype q _ _ (x q !)) _ _ ((e0 q α).(ce_t))).
refine (@itype_in q (yft0 (A0 q α) q !) (fun αi => (e0 q α).(ce_f0) q (merge ! αi))).
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
refine (fun q α αi => _).
change (yft1 (A0 q α) q ! (fun r β => cast0 A0 A1 α β (itype_out (anticompare0 A0 A1 x0 x1 y0 y1 e0 e1 r (α ∘ β)) (αi ∘ β)))).
unfold anticompare0.
pose proof (e1 q α). simpl in H. unfold cube_eqR in H. unfold cast0 in H. simpl in H.
refine (J_seqs _ _ (fun X _ =>
  yft1 (A0 q α) q ! (fun r β => cast0 A0 A1 α β (itype_out
    (J_seq _ _
      (fun x (_ : side_0 ⋅ ce_f0 (X r β) ≡ x) =>
        itype r (yft0 (A0 r (α ∘ β)) r !)
          (x r !) (y0 r ((α ∘ β) ∘ !)))
      (J_seq _ _
        (fun x (_ : side_1 ⋅ ce_f0 (X r β) ≡ x) =>
          itype r (yft0 (A0 r (α ∘ β)) r !)
            (ce_f0 (X r β) r side_0) (x r !))
        (@itype_in r (yft0 (A0 r (α ∘ β)) r !) (fun αi0 : r ≤ 1 => ce_f0 (X r β) r (merge ! αi0)))
        (α ∘ β ⋅ y0) (ce_t (X r β)))
      (α ∘ β ⋅ x0) (ce_s (X r β)))
    (αi ∘ β)))) _ _ (ssym H)). simpl.
pose proof (ce_t (e0 q α)).
refine (J_seqs _ _ (fun X E =>
  yft1 (A0 q α) q !
    (fun (r : nat) (β : r ≤ q) =>
     cast0 A0 A1 α β
       (itype_out
          (J_seq _ _
             (fun (x : forall (x2 : nat) (x3 : x2 ≤ r), yft0 (A0 x2 ((α ∘ β) ∘ (squish ∘ (side_0 ∘ x3)))) x2 !)
                (_ : (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (promote β ∘ (side_0 ∘ β0))) ≡ x)
              => itype r (yft0 (A0 r (α ∘ β)) r !) (x r !) (X r β))
             (J_seq _ _
                (fun
                   (x : forall (x2 : nat) (x3 : x2 ≤ r), yft0 (A0 x2 ((α ∘ β) ∘ (squish ∘ (side_1 ∘ x3)))) x2 !)
                   (_ : (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (promote β ∘ (side_1 ∘ β0))) ≡ x)
                 => itype r (yft0 (A0 r (α ∘ β)) r !) (ce_f0 (e0 q (α ∘ !)) r (promote β ∘ side_0)) (x r !))
                (@itype_in r (yft0 (A0 r (α ∘ β)) r !)
                   (fun αi0 : r ≤ 1 => ce_f0 (e0 q (α ∘ !)) r (promote β ∘ merge ! αi0)))
                (β ⋅ X)
                (J_seqs _ _
                   (fun (u : forall (x2 : nat) (x3 : x2 ≤ q), yft0 (A0 x2 ((α ∘ !) ∘ (! ∘ x3))) x2 !)
                      (_ : side_1 ⋅ ce_f0 (e0 q (α ∘ !)) ≡ u) =>
                    (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (side_1 ∘ (β ∘ β0))) ≡ β ⋅ u)
                   (srefl (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (side_1 ∘ (β ∘ β0))))
                   X E))
             (α ∘ β ⋅ x0)
             (J_seqs _ _
                (fun (u : forall (x2 : nat) (x3 : x2 ≤ q), yft0 (A0 x2 ((α ∘ !) ∘ (! ∘ x3))) x2 !)
                   (_ : side_0 ⋅ ce_f0 (e0 q (α ∘ !)) ≡ u) =>
                 (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (side_0 ∘ (β ∘ β0))) ≡ β ⋅ u)
                (srefl (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (side_0 ∘ (β ∘ β0))))
                (fun (r0 : nat) (β0 : r0 ≤ q) => x0 r0 ((α ∘ !) ∘ (! ∘ β0))) (ce_s (e0 q (α ∘ !)))))
          (αi ∘ β)))) _ _ (ce_t (e0 q α))). simpl.
refine (J_seqs _ _ (fun X E =>
  yft1 (A0 q α) q !
    (fun (r : nat) (β : r ≤ q) =>
     cast0 A0 A1 α β
       (itype_out
          (J_seq (forall (x2 : nat) (x3 : x2 ≤ r), yft0 (A0 x2 ((α ∘ β) ∘ (squish ∘ (side_0 ∘ x3)))) x2 !)
             (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (promote β ∘ (side_0 ∘ β0)))
             (fun (x : forall (x2 : nat) (x3 : x2 ≤ r), yft0 (A0 x2 ((α ∘ β) ∘ (squish ∘ (side_0 ∘ x3)))) x2 !)
                (_ : (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (promote β ∘ (side_0 ∘ β0))) ≡ x)
              => itype r (yft0 (A0 r (α ∘ β)) r !) (x r !) (ce_f0 (e0 q (α ∘ !)) r (side_1 ∘ β)))
             (@itype_in r (yft0 (A0 r (α ∘ β)) r !)
                (fun αi0 : r ≤ 1 => ce_f0 (e0 q (α ∘ !)) r (promote β ∘ merge ! αi0)))
             (β ⋅ X)
             (J_seqs (forall (x2 : nat) (x3 : x2 ≤ q), yft0 (A0 x2 ((α ∘ !) ∘ (! ∘ x3))) x2 !)
                (side_0 ⋅ ce_f0 (e0 q (α ∘ !)))
                (fun (u : forall (x2 : nat) (x3 : x2 ≤ q), yft0 (A0 x2 ((α ∘ !) ∘ (! ∘ x3))) x2 !)
                   (_ : side_0 ⋅ ce_f0 (e0 q (α ∘ !)) ≡ u) =>
                 (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (side_0 ∘ (β ∘ β0))) ≡ β ⋅ u)
                (srefl (fun (r0 : nat) (β0 : r0 ≤ r) => ce_f0 (e0 q (α ∘ !)) r0 (side_0 ∘ (β ∘ β0))))
                X E))
          (αi ∘ β)))) _ _ (ce_s (e0 q α))). simpl.
refine (J_seqs _ _
  (fun x _ => yft1 (A0 q α) q ! (fun r β => cast0 A0 A1 α β (x r (yft0 (A0 r (α ∘ β)) r !) (fun αi0 : r ≤ 1 => ce_f0 (e0 q α) r (promote β ∘ merge ! αi0)) (αi ∘ β)))) _ _
               (ssym itype_inout)).
refine ((e0 q α).(ce_f1) q (merge ! αi)).
Defined.


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
unshelve refine (compare0 (Arr0 A0 A1 B0 B1) (Arr1 A0 A1 B0 B1) f0 f1 g0 g1 _ _).
unshelve refine (path_funext0 A0 A1 B0 B1 f0 f1 g0 g1 _ _).
refine (fun q α x0 x1 => _).
refine (anticompare0 (α ⋅ B0) (α ⋅ B1)
  (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
  (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1)
  (@dapp0 q (α ⋅ A0) (α ⋅ A1)
    (fun r β y0 y1 => eq0 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (fun r β y0 y1 => eq1 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (α ⋅ h0) x0 x1)
  (@dapp1 q (α ⋅ A0) (α ⋅ A1)
    (fun r β y0 y1 => eq0 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (fun r β y0 y1 => eq1 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (α ⋅ h0) (α ⋅ h1) x0 x1) q !).
refine (fun q α x0 x1 => _).
refine (anticompare1 (α ⋅ B0) (α ⋅ B1)
  (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
  (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1)
  (@dapp0 q (α ⋅ A0) (α ⋅ A1)
    (fun r β y0 y1 => eq0 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (fun r β y0 y1 => eq1 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (α ⋅ h0) x0 x1)
  (@dapp1 q (α ⋅ A0) (α ⋅ A1)
  (fun r β y0 y1 => eq0 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
    (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
    (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
  (fun r β y0 y1 => eq1 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
    (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
    (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
  (α ⋅ h0) (α ⋅ h1) x0 x1) q !).
unshelve refine (path_funext1 A0 A1 B0 B1 f0 f1 g0 g1
  (fun q α x0 x1 => anticompare0 (α ⋅ B0) (α ⋅ B1)
  (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
  (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1)
  (@dapp0 q (α ⋅ A0) (α ⋅ A1)
    (fun r β y0 y1 => eq0 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (fun r β y0 y1 => eq1 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (α ⋅ h0) x0 x1)
  (@dapp1 q (α ⋅ A0) (α ⋅ A1)
    (fun r β y0 y1 => eq0 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (fun r β y0 y1 => eq1 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (α ⋅ h0) (α ⋅ h1) x0 x1) q !)
   (fun q α x0 x1 => anticompare1 (α ⋅ B0) (α ⋅ B1)
  (app0 (α ⋅ f0) x0 x1) (app1 (α ⋅ f1) x0 x1)
  (app0 (α ⋅ g0) x0 x1) (app1 (α ⋅ g1) x0 x1)
  (@dapp0 q (α ⋅ A0) (α ⋅ A1)
    (fun r β y0 y1 => eq0 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (fun r β y0 y1 => eq1 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
      (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
      (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
    (α ⋅ h0) x0 x1)
  (@dapp1 q (α ⋅ A0) (α ⋅ A1)
  (fun r β y0 y1 => eq0 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
    (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
    (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
  (fun r β y0 y1 => eq1 (α ∘ β ⋅ B0) (α ∘ β ⋅ B1)
    (app0 (α ∘ β ⋅ f0) y0 y1) (app1 (α ∘ β ⋅ f1) y0 y1)
    (app0 (α ∘ β ⋅ g0) y0 y1) (app1 (α ∘ β ⋅ g1) y0 y1) r !)
  (α ⋅ h0) (α ⋅ h1) x0 x1) q !)).
Defined.


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