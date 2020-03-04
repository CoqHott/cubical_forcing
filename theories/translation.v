From Theories Require Import category.

Set Primitive Projections.
Set Universe Polymorphism.
Set Polymorphic Inductive Cumulativity.

Record TYPE@{i} (p : ℙ) := mkTYPE {
  typ : forall q (α : q ≤ p), Type@{i};
  rel : (forall q (α : q ≤ p), typ q α) -> SProp;
}.

Arguments typ {_}.
Arguments rel {_}.

Definition El {p : ℙ} (A : forall q (α : q ≤ p), TYPE q) :=
  forall q (α : q ≤ p), (A q α).(typ) q !.

Definition cast : forall {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  {q} (α : q ≤ p) {r} (β : r ≤ q), (A r (α ∘ β)).(typ) r ! -> (A q α).(typ) r β.
Proof.
refine (fun p A Aε q α r β x => _).
refine (J_seq _ _ (fun X _ => X -> (A q α).(typ) r β) (fun r => r) _ (Aε q α r β) x).
Defined.

Definition Elε {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q),
    (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (x : El A)
  :=
  forall q (α : q ≤ p),
    (A q α).(rel) (fun r (β : r ≤ q) => cast A Aε α β (x r (α ∘ β))).

Definition Typeᶠ {p} : forall q (α : q ≤ p), TYPE q.
Proof.
unshelve econstructor.
+ refine (fun r β => TYPE r).
+ unshelve refine (fun A =>
  forall r (β : r ≤ q),
    (A q !).(typ) r β ≡ (A r β).(typ) r !).
Defined.

(* Hard-wired, it requires definitional UIP to type-check *)
Definition TypeR {p : ℙ}
  (A : forall q (α : q ≤ p), TYPE q) : SProp :=
  forall q (α : q ≤ p) r (β : r ≤ q),
    (A q α).(typ) r β ≡ (A r (α ∘ β) ).(typ) r !.

Definition Typeε {p} : @TypeR p Typeᶠ.
Proof.
intros q α r β.
reflexivity.
Defined.

Goal forall p A, TypeR A = @Elε p  Typeᶠ Typeε A.
Proof.
reflexivity.
Abort.

Definition Arr {p} : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B),
  @El p Typeᶠ.
Proof.
unshelve refine (fun A Aε B Bε q α => mkTYPE _ _ _).
+ unshelve refine (fun r β =>
  forall
  (x : El (α ∘ β · A))
  (xε : Elε (α ∘ β · A) (α ∘ β · Aε) x)
  ,
  (B r (α ∘ β)).(typ) r !).
+ unshelve refine (fun f =>
  forall
  (x : El (α · A))
  (xε : Elε (α · A) (α · Aε) x)
  ,
  (B q α).(rel) (fun r β =>
    cast B Bε α _ (f r β (β · x) (β · xε)))
).
Defined.

Definition Arrε {p} : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B),
  Elε Typeᶠ Typeε (Arr A Aε B Bε).
Proof.
intros A Aε B Bε q α r β.
reflexivity.
Defined.

Definition lamᶠ {p A Aε B Bε}
  (f : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x), El (α · B))
: El (Arr A Aε B Bε).
Proof.
refine (fun q α x xε => _).
unshelve refine (f q α x xε q !).
Defined.

Definition lamε {p A Aε B Bε f}
  (fε : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x),
    Elε (α · B) (α · Bε) (f q α x xε))
: Elε (Arr A Aε B Bε) (Arrε A Aε B Bε) (lamᶠ f).
Proof.
refine (fun q α x xε => _).
unshelve refine (fε q α x xε q !).
Defined.

Definition appᶠ {p A Aε B Bε} (f : @El p (Arr A Aε B Bε)) (x : El A) (xε : Elε A Aε x) : El B.
Proof.
refine (fun q α => f q α (α · x) (α · xε)).
Defined.

Definition appε {p A Aε B Bε} {f : @El p (Arr A Aε B Bε)}
  (fε : Elε _ (Arrε A Aε B Bε) f) (x : El A) (xε : Elε A Aε x) : Elε B Bε (appᶠ f x xε).
Proof.
refine (fun q α => fε _ _ (α · x) (α · xε)).
Defined.

(*
Goal forall p
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
  f (x : El A) (xε : Elε A Aε x) q (α : q ≤ p),
  @appᶠ p A Aε B Bε (lamᶠ f) x xε q α = f q α (α · x) (α · xε) q !.
Proof.
reflexivity.
Abort.
*)

Definition Prod {p} : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p (Arr A Aε Typeᶠ Typeε))
  (Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B),
  @El p Typeᶠ.
Proof.
unshelve refine (fun A Aε B Bε q α => mkTYPE _ _ _).
+ unshelve refine (fun r β =>
  forall
  (x : El (α ∘ β · A))
  (xε : Elε (α ∘ β · A) (α ∘ β · Aε) x)
  ,
  (B r (α ∘ β) x xε).(typ) r !).
+ unshelve refine (fun f =>
  forall
  (x : El (α · A))
  (xε : Elε (α · A) (α · Aε) x)
  ,
  (B q α x xε).(rel) _
).
unshelve refine (fun r β => @cast q
  (fun s (γ : s ≤ q) => B s (α ∘ γ) (γ · x) (γ · xε))
  (fun s (γ : s ≤ q) => Bε s (α ∘ γ) (γ · x) (γ · xε))
  _ ! _ β (f r _ (β · x) (β · xε))).
Defined.

Definition Prodε {p} : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : El (Arr A Aε Typeᶠ Typeε))
  (Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B),
  Elε Typeᶠ Typeε (Prod A Aε B Bε)
.
Proof.
refine (fun A Aε B Bε q α r β => _).
reflexivity.
Defined.

Definition dlamᶠ {p}
  {A Aε}
  {B : El (Arr A Aε Typeᶠ Typeε)}
  {Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B}
  (f : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x), El (appᶠ (α · B) x xε))
  : El (Prod A Aε B Bε).
Proof.
refine (fun q α x xε => f q α x xε q !).
Defined.

Definition dlamε {p}
  {A Aε}
  {B : El (Arr A Aε Typeᶠ Typeε)}
  {Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B}
  {f : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x), El (appᶠ (α · B) x xε)}
  (fε : forall q (α : q ≤ p) (x : El (α · A)) (xε : Elε (α · A) (α · Aε) x),
    Elε (appᶠ (α · B) x xε) (@appε q (α · A) (α · Aε) (α · Typeᶠ) (α · Typeε) (α · B) (α · Bε) x xε) (f q α x xε))
  : Elε (Prod A Aε B Bε) (Prodε A Aε B Bε) (dlamᶠ f).
Proof.
refine (fun q α x xε => fε q α x xε q !).
Defined.

Definition dappᶠ {p}
           {A Aε}
           {B : El (Arr A Aε Typeᶠ Typeε)}
           {Bε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) B}
           (f : El (Prod A Aε B Bε))
           (x : El A) (xε : Elε A Aε x) :
  @El p (appᶠ B x xε).
Proof.
  intros q α.
  exact (f q α (α · x) (α · xε)).
Defined.

Definition dappε {p}
           {A Aε}
           {B : El (Arr A Aε Typeᶠ Typeε)}
           {Bε : Elε _ (Arrε A Aε Typeᶠ Typeε) B}
           (f : El (Prod A Aε B Bε))
           (fε : Elε _ (Prodε A Aε B Bε) f)
           (x : El A) (xε : Elε A Aε x) :
  Elε (appᶠ B x xε) (appε Bε x xε) (@dappᶠ p A Aε B Bε f x xε).
Proof.
  intros q α.
  exact (fε q α (α · x) (α · xε)).
Defined.

Inductive sum_ {p}
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
:=
| inl_ : forall
  (x : El A)
  (xε : Elε A Aε x),
  sum_ A Aε B Bε
| inr_ : forall
  (y : El B)
  (yε : Elε B Bε y),
  sum_ A Aε B Bε
.

Inductive sumR p
  (A : @El p Typeᶠ)
  (Aε : TypeR A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
  : (forall q (α : q ≤ p), @sum_ q (α · A) (α · Aε) (α · B) (α · Bε)) -> SProp :=
| inlR : forall
  (x : El A)
  (xε : Elε A Aε x),
  sumR p A Aε B Bε (fun q α => @inl_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · x) (α · xε))
| inrR : forall
  (y : El B)
  (yε : Elε B Bε y),
  sumR p A Aε B Bε (fun q α => @inr_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · y) (α · yε))
.

Definition sumᶠ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B) : @El p Typeᶠ :=
  fun q (α : q ≤ p) => mkTYPE q
    (fun r β => @sum_ r (α ∘ β · A) (α ∘ β · Aε) (α ∘ β · B) (α ∘ β · Bε))
    (fun v => sumR q (α · A) (α · Aε) (α · B) (α · Bε) v).

Definition inlᶠ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B)
  (x : El A)
  (xε : Elε A Aε x)

  : El (sumᶠ A Aε B Bε).
Proof.
refine (fun q α => inl_ _ _ _ _ (α · x) (α · xε)).
Defined.

Definition inrᶠ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B)
  (y : El B)
  (yε : Elε B Bε y)

  : El (sumᶠ A Aε B Bε).
Proof.
refine (fun q α => inr_ _ _ _ _ (α · y) (α · yε)).
Defined.

Definition sumε {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B) : Elε Typeᶠ Typeε (sumᶠ A Aε B Bε).
Proof.
unfold Elε; cbn.
reflexivity.
Defined.

Definition inlε {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B)
  (x : El A)
  (xε : Elε A Aε x)

  : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) (inlᶠ A Aε B Bε x xε).
Proof.
refine (fun q α => inlR _ _ _ _ _ (α · x) (α · xε)).
Defined.

Definition inrε {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ) (Bε : Elε Typeᶠ Typeε B)
  (y : El B)
  (yε : Elε B Bε y)

  : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) (inrᶠ A Aε B Bε y yε).
Proof.
refine (fun q α => inrR _ _ _ _ _ (α · y) (α · yε)).
Defined.


Definition sum_inv {p A Aε B Bε}
  (b : @El p (sumᶠ A Aε B Bε))
  (bε : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) b) :
match b p ! with
| inl_ _ _ _ _ x xε => (fun q α => @inl_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · x) (α · xε)) ≡ b
| inr_ _ _ _ _ y yε => (fun q α => @inr_ q (α · A) (α · Aε) (α · B) (α · Bε) (α · y) (α · yε)) ≡ b
end.
Proof.
pose proof (bε p !) as bε'. cbn in *.
change (! · b) with b in bε'. destruct bε'.
- reflexivity.
- reflexivity.
Defined.

Definition sum_elim p : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
  (P : El (Arr (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε))
  (Pε : Elε
    (Arr (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε)
    (Arrε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε) P)

  (ul : El (Prod A Aε
    (fun q α x xε => P q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
    (fun q α x xε => Pε q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
  ))

  (ulε : Elε _ (Prodε A Aε
    (fun q α x xε => P q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
    (fun q α x xε => Pε q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
  ) ul)

  (ur : El (Prod B Bε
    (fun q α y yε => P q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
    (fun q α y yε => Pε q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
  ))

  (urε : Elε _ (Prodε B Bε
    (fun q α y yε => P q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
    (fun q α y yε => Pε q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
  ) ur)

  (b : @El p (sumᶠ A Aε B Bε))
  (bε : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) b),

 forall q (α : q ≤ p),
 (P q α (α · b) (α · bε)).(typ) q !.
Proof.
  intros.
assert (be := @sum_inv p A Aε B Bε b bε).
destruct (b p !) as [x xε|y yε].
+ destruct be.
 refine (ul q α (α · x) (α · xε)).
+ destruct be.
 refine (ur q α (α · y) (α · yε)).
Defined.

Definition sum_elimε p : forall
  (A : @El p Typeᶠ)
  (Aε : Elε Typeᶠ Typeε A)
  (B : @El p Typeᶠ)
  (Bε : Elε Typeᶠ Typeε B)
  (P : El (Arr (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε))
  (Pε : Elε
    (Arr (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε)
    (Arrε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) Typeᶠ Typeε) P)

  (ul : El (Prod A Aε
    (fun q α x xε => P q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
    (fun q α x xε => Pε q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
  ))

  (ulε : Elε _ (Prodε A Aε
    (fun q α x xε => P q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
    (fun q α x xε => Pε q α _ (inlε (α · A) (α · Aε) (α · B) (α · Bε) x xε))
  ) ul)

  (ur : El (Prod B Bε
    (fun q α y yε => P q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
    (fun q α y yε => Pε q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
  ))

  (urε : Elε _ (Prodε B Bε
    (fun q α y yε => P q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
    (fun q α y yε => Pε q α _ (inrε (α · A) (α · Aε) (α · B) (α · Bε) y yε))
  ) ur)

  (b : @El p (sumᶠ A Aε B Bε))
  (bε : Elε (sumᶠ A Aε B Bε) (sumε A Aε B Bε) b),

 Elε _ (appε Pε b bε) (sum_elim _ _ _ _ _ _ _ ul ulε ur urε b bε).
Proof.
intros.
intros q α; cbn.
unfold appᶠ, sum_elim.
cbn.
set (b₀ := b p !).
Abort.

Definition K p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  (x : El A)
  (xε : Elε A Aε x)
  (y : El B)
  (xε : Elε B Bε y)
  q (α : q ≤ p)
,
(A q α).(typ) q !.
Proof.
refine (fun A Aε B Bε x xε y yε q α => x q α).
Defined.

Definition Kε p : forall
  (A : forall q (α : q ≤ p), TYPE q)
  (Aε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (A q α).(typ) r β ≡ (A r (α ∘ β)).(typ) r !)
  (B : forall q (α : q ≤ p), TYPE q)
  (Bε : forall q (α : q ≤ p),
    forall r (β : r ≤ q), (B q α).(typ) r β ≡ (B r (α ∘ β)).(typ) r !)
  (x : El A)
  (xε : Elε A Aε x)
  (y : El B)
  (yε : Elε B Bε y)
  q (α : q ≤ p)
,
  (A q α).(rel) (fun r β => cast A Aε α β (K p A Aε B Bε x xε y yε r (α ∘ β))).
Proof.
intros.
apply xε.
Defined.

(* Empty type *)

Inductive empty : Type :=.

Definition emptyᶠ {p} : @El p Typeᶠ.
Proof.
unshelve refine (fun q α => mkTYPE _ _ _).
+ unshelve refine (fun r β => empty).
+ unshelve refine (fun _ => sTrue).
Defined.

Definition emptyε {p : ℙ} : @Elε p Typeᶠ Typeε (emptyᶠ).
Proof.
unfold Elε. cbn. reflexivity.
Defined.

Definition empty_elimᶠ {p}
  (P : El (Arr emptyᶠ emptyε Typeᶠ Typeε))
  (Pε : Elε (Arr emptyᶠ emptyε Typeᶠ Typeε) (Arrε emptyᶠ emptyε Typeᶠ Typeε) P)
  (x : @El p emptyᶠ)
  (xε : Elε emptyᶠ emptyε x) :
  El (appᶠ P x xε).
Proof.
unshelve refine (fun q α => _).
destruct (x q α).
Defined.

Definition empty_elimε {p}
  (P : El (Arr emptyᶠ emptyε Typeᶠ Typeε))
  (Pε : Elε (Arr emptyᶠ emptyε Typeᶠ Typeε) (Arrε emptyᶠ emptyε Typeᶠ Typeε) P)
  (x : @El p emptyᶠ)
  (xε : Elε emptyᶠ emptyε x) :
  Elε _ (appε Pε x xε) (empty_elimᶠ P Pε x xε).
Proof.
unshelve refine (fun q α => _).
destruct (x q α).
Defined.

(* equality *)

Inductive eq_ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (x : @El p A) (xε : Elε A Aε x) :
  forall (y : @El p A) (yε : Elε A Aε y), Type :=
| refl_ : eq_ A Aε x xε x xε.

Inductive eqR {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (x : @El p A) (xε : Elε A Aε x) :
  forall (y : @El p A) (yε : Elε A Aε y),
  (forall (q : ℙ) (α : q ≤ p), eq_ (α · A) (α · Aε) (α · x) (α · xε) (α · y) (α · yε))
  -> SProp :=
| reflR : eqR A Aε x xε x xε (fun q α => refl_ (α · A) (α · Aε) (α · x) (α · xε)).

Definition eqᶠ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (x : @El p A) (xε : Elε A Aε x)
  (y : @El p A) (yε : Elε A Aε y) :
  @El p Typeᶠ.
Proof.
unshelve refine (fun q α => mkTYPE _ _ _).
+ refine (fun r β => eq_ (α ∘ β · A) (α ∘ β · Aε)
                         (α ∘ β · x) (α ∘ β · xε)
                         (α ∘ β · y) (α ∘ β · yε)).
+ refine (eqR (α · A) (α · Aε) (α · x) (α · xε) (α · y) (α · yε)).
Defined.

Definition eqε {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (x : @El p A) (xε : Elε A Aε x)
  (y : @El p A) (yε : Elε A Aε y) :
  Elε Typeᶠ Typeε (eqᶠ A Aε x xε y yε).
Proof.
unfold Elε. cbn. reflexivity.
Defined.

Definition reflᶠ  {p}
           {A : @El p Typeᶠ} {Aε : Elε Typeᶠ Typeε A}
           (x : @El p A) (xε : Elε A Aε x) :
  @El p (eqᶠ A Aε x xε x xε).
Proof.
  intros q α.
  unfold eqᶠ. cbn.
  exact(refl_ _ _ (α · x) (α · xε)).
Defined.

Definition reflε {p}
           {A : @El p Typeᶠ} {Aε : Elε Typeᶠ Typeε A}
           (x : @El p A) (xε : Elε A Aε x) :
  @Elε p _ (eqε A Aε x xε x xε) (reflᶠ x xε).
Proof.
  intros q α.
  apply reflR.
Defined.

Definition eq_transpᶠ {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (P : El (Arr A Aε Typeᶠ Typeε)) (Pε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) P)
  (x : @El p A) (xε : Elε A Aε x)
  (y : @El p A) (yε : Elε A Aε y)
  (e : @El p (eqᶠ A Aε x xε y yε)) (eε : Elε (eqᶠ A Aε x xε y yε) (eqε A Aε x xε y yε) e)
  (a : @El p (appᶠ P x xε)) (aε : Elε (appᶠ P x xε) (appε Pε x xε) a) :
  @El p (appᶠ P y yε).
Proof.
  intros q α.
  clear eε. specialize (e p !). simpl in e.
  change (! ∘ ?f) with f in *. change (! · ?f) with f in *.
  destruct e. exact (a q α).
Defined.

Definition eq_transpε {p}
  (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
  (P : El (Arr A Aε Typeᶠ Typeε)) (Pε : Elε (Arr A Aε Typeᶠ Typeε) (Arrε A Aε Typeᶠ Typeε) P)
  (x : @El p A) (xε : Elε A Aε x)
  (y : @El p A) (yε : Elε A Aε y)
  (e : @El p (eqᶠ A Aε x xε y yε)) (eε : Elε (eqᶠ A Aε x xε y yε) (eqε A Aε x xε y yε) e)
  (a : @El p (appᶠ P x xε)) (aε : Elε (appᶠ P x xε) (appε Pε x xε) a) :
  @Elε p (appᶠ P y yε) (appε Pε y yε) (eq_transpᶠ A Aε P Pε x xε y yε e eε a aε).
Proof.
  unfold eq_transpᶠ.
  set (ep := e p !).
  clearbody ep. simpl in ep. change (! ∘ ?f) with f in *. change (! · ?f) with f in *.
  destruct ep. simpl.
  exact aε.
Defined.


(* J should be the same but slightly worse. *)
Check eq_rect.
Definition Jᶠ {p}
           {A : @El p Typeᶠ} {Aε : Elε Typeᶠ Typeε A}
           {x : @El p A} (xε : Elε A Aε x)
           {P : El (Prod A Aε _
                         (lamε (fun q α y yε =>
                                  Arrε _ (eqε (α · A) (α · Aε) (α · x) (α · xε) y yε) Typeᶠ Typeε)
                         )
                   )
           }
           (Pε : Elε _
                     (Prodε A Aε _
                            (lamε (fun q α y yε =>
                                     Arrε _ (eqε (α · A) (α · Aε) (α · x) (α · xε) y yε) Typeᶠ Typeε)
                            )
                     )
                     P
           )
           {y : @El p A} (yε : Elε A Aε y)
           {e : @El p (eqᶠ A Aε x xε y yε)} (eε : Elε _ (eqε A Aε x xε y yε) e)
           (H : El  (appᶠ (dappᶠ P x xε) (reflᶠ x xε) (reflε x xε)))
  : El (appᶠ (dappᶠ P y yε) e eε) .
Proof.
  assert (t := eε p !).
  change  (eqR A Aε x xε y yε e) in t. destruct t.
  exact H.
Defined.


Definition Jε {p}
           (A : @El p Typeᶠ) (Aε : Elε Typeᶠ Typeε A)
           (x : @El p A) (xε : Elε A Aε x)
           (P : El (Prod A Aε _
                         (lamε (fun q α y yε =>
                                  Arrε _ (eqε (α · A) (α · Aε) (α · x) (α · xε) y yε) Typeᶠ Typeε)
                         )
                   )
           )
           (Pε : Elε _
                     (Prodε A Aε _
                            (lamε (fun q α y yε =>
                                     Arrε _ (eqε (α · A) (α · Aε) (α · x) (α · xε) y yε) Typeᶠ Typeε)
                            )
                     )
                     P
           )
           (y : @El p A) (yε : Elε A Aε y)
           (e : @El p (eqᶠ A Aε x xε y yε)) (eε : Elε _ (eqε A Aε x xε y yε) e)
           (H : El (appᶠ (dappᶠ P x xε) (reflᶠ x xε) (reflε x xε)))
           (Hε : Elε _ (appε (dappε P Pε x xε) (reflᶠ x xε) (reflε x xε)) H)
  : Elε (appᶠ (dappᶠ P y yε) e eε) (appε (dappε P Pε y yε) e eε) (Jᶠ xε Pε yε eε H).
Proof.
  assert (t := eε p !).
  change  (eqR A Aε x xε y yε e) in t. destruct t.
  exact Hε.
Defined.

(* Classifying presheaf for SProps *)

Record sieve (p : ℙ) := mkSieve {
  styp : forall q (α : q ≤ p), SProp;
  srel : (forall q (α : q ≤ p), styp q α) -> SProp;
}.

Arguments styp {_}.
Arguments srel {_}.

Definition Ωᶠ {p} : @El p Typeᶠ.
Proof.
unshelve refine (fun q α => mkTYPE _ _ _).
+ unshelve refine (fun r β => sieve r).
+ unshelve refine (fun A =>
  forall r (β : r ≤ q),
    (A q !).(styp) r β ≡ (A r β).(styp) r !).
Defined.

Definition Ωε {p : ℙ} : @Elε p Typeᶠ Typeε Ωᶠ.
Proof.
unfold Elε ; cbn.
reflexivity.
Defined.

(* squashing prehseaves *)

Inductive squash (X : Type) : SProp :=
| squashed : forall x : X, squash X.

Inductive squash_ {p : ℙ}
  (X : @El p Typeᶠ) (Xε : Elε Typeᶠ Typeε X) : SProp :=
| squashed_ : forall (x : @El p X) (xε : Elε X Xε x), squash_ X Xε.

Inductive squashR {p : ℙ}
  (X : @El p Typeᶠ) (Xε : Elε Typeᶠ Typeε X) :
  (forall q (α : q ≤ p), @squash_ q (α · X) (α · Xε)) -> SProp :=
| squashedR : forall (x : @El p X) (xε : Elε X Xε x),
  squashR X Xε (fun q (α : q ≤ p) => @squashed_ q (α · X) (α · Xε) (α · x) (α · xε)).

Definition squashᶠ {p : ℙ}
  (X : @El p Typeᶠ) (Xε : Elε Typeᶠ Typeε X) :
  @El p Ωᶠ.
Proof.
unshelve refine (fun q α => _).
unshelve econstructor.
- exact (fun r β => @squash_ r (α ∘ β · X) (α ∘ β · Xε)).
- exact (fun s => @squashR q (α · X) (α · Xε) s).
Defined.

Definition squashε {p : ℙ}
  (X : @El p Typeᶠ) (Xε : Elε Typeᶠ Typeε X) :
  @Elε p Ωᶠ Ωε (squashᶠ X Xε).
Proof.
unfold Elε. simpl. reflexivity.
Defined.
