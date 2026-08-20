import Mathlib

/-!
# Inaccessible Implies Con ZFC
Category: Frontier — Set Theory
Target: Frontier.inaccessible_implies_ConZFC
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

universe u

namespace Frontier

open FirstOrder Language ZFSet Ordinal Cardinal Order Set

/-! ## Cardinal arithmetic of the von Neumann hierarchy below an inaccessible -/

variable {κ : Cardinal.{u}}

/-- Below an inaccessible cardinal `κ`, all the beth-numbers are smaller than `κ`. -/
theorem preBeth_lt_of_isInaccessible (hκ : κ.IsInaccessible) :
    ∀ o : Ordinal.{u}, o < κ.ord → preBeth o < κ := by
  intro o
  induction o using Ordinal.induction with
  | _ o IH =>
    intro ho
    rw [Cardinal.preBeth]
    have he : (⨆ a : Iio o, (2 : Cardinal.{u}) ^ preBeth a)
        = ⨆ i : o.ToType, (2 : Cardinal.{u}) ^ preBeth ((Ordinal.ToType.mk (o := o)).symm i) :=
      (Equiv.iSup_comp (g := fun a : Iio o => (2 : Cardinal.{u}) ^ preBeth a)
        (Ordinal.ToType.mk (o := o)).symm.toEquiv).symm
    rw [he]
    refine Ordinal.iSup_lt ?_ fun i => ?_
    · rw [mk_toType, hκ.isRegular.cof_eq]
      exact Cardinal.lt_ord.mp ho
    · exact hκ.isStrongLimit.two_power_lt (IH _ ((Ordinal.ToType.mk (o := o)).symm i).2
        (((Ordinal.ToType.mk (o := o)).symm i).2.trans ho))

/-- Every set in `V_κ` has cardinality less than `κ`, for `κ` inaccessible. -/
theorem card_lt_of_mem_vonNeumann (hκ : κ.IsInaccessible) {x : ZFSet.{u}}
    (hx : x ∈ vonNeumann κ.ord) : x.card < κ := by
  have h1 : x.card ≤ (vonNeumann (rank x)).card := card_mono (subset_vonNeumann_self x)
  rw [card_vonNeumann] at h1
  exact h1.trans_lt (preBeth_lt_of_isInaccessible hκ _ (ZFSet.mem_vonNeumann.mp hx))

theorem isSuccLimit_ord (hκ : κ.IsInaccessible) : IsSuccLimit κ.ord :=
  Cardinal.isSuccLimit_ord hκ.aleph0_lt.le

/-! ## Closure properties of `V_κ` for `κ` inaccessible -/

theorem empty_mem_vonNeumann (hκ : κ.IsInaccessible) : (∅ : ZFSet.{u}) ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann, rank_empty]
  exact (isSuccLimit_ord hκ).bot_lt

theorem pair_mem_vonNeumann (hκ : κ.IsInaccessible) {x y : ZFSet.{u}}
    (hx : x ∈ vonNeumann κ.ord) (hy : y ∈ vonNeumann κ.ord) :
    ({x, y} : ZFSet) ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann] at *
  rw [rank_pair]
  exact max_lt ((isSuccLimit_ord hκ).succ_lt hx) ((isSuccLimit_ord hκ).succ_lt hy)

theorem sUnion_mem_vonNeumann {o : Ordinal.{u}} {x : ZFSet.{u}} (hx : x ∈ vonNeumann o) :
    (⋃₀ x) ∈ vonNeumann o := by
  rw [ZFSet.mem_vonNeumann] at *
  exact (rank_sUnion_le x).trans_lt hx

theorem powerset_mem_vonNeumann (hκ : κ.IsInaccessible) {x : ZFSet.{u}}
    (hx : x ∈ vonNeumann κ.ord) : x.powerset ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann] at *
  rw [rank_powerset]
  exact (isSuccLimit_ord hκ).succ_lt hx

theorem sep_mem_vonNeumann {o : Ordinal.{u}} {x : ZFSet.{u}} (p : ZFSet.{u} → Prop)
    (hx : x ∈ vonNeumann o) : ZFSet.sep p x ∈ vonNeumann o :=
  mem_vonNeumann_of_subset sep_subset hx

theorem subset_mem_vonNeumann {o : Ordinal.{u}} {x y : ZFSet.{u}} (h : x ⊆ y)
    (hy : y ∈ vonNeumann o) : x ∈ vonNeumann o :=
  mem_vonNeumann_of_subset h hy

theorem rank_ofNat (n : ℕ) : PSet.rank (PSet.ofNat n) = (n : Ordinal) := by
  induction n with
  | zero => exact PSet.rank_empty
  | succ n ih =>
    rw [PSet.ofNat, PSet.rank_insert, ih, max_eq_left (Order.le_succ _), Order.succ_eq_add_one,
      Nat.cast_add, Nat.cast_one]

theorem rank_omega_le : rank ZFSet.omega.{u} ≤ Ordinal.omega0 := by
  show PSet.rank PSet.omega ≤ _
  rw [PSet.omega, PSet.rank]
  refine Ordinal.iSup_le fun a => ?_
  rw [rank_ofNat]
  exact Order.succ_le_of_lt (Ordinal.nat_lt_omega0 _)

theorem omega_mem_vonNeumann (hκ : κ.IsInaccessible) : ZFSet.omega.{u} ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann]
  refine rank_omega_le.trans_lt ?_
  have : (ℵ₀ : Cardinal.{u}).ord < κ.ord := Cardinal.ord_lt_ord.mpr hκ.aleph0_lt
  rwa [Cardinal.ord_aleph0] at this

/-- Replacement: `V_κ` is closed under images of its elements, for `κ` inaccessible.  This is
where the regularity of `κ` is used. -/
theorem range_mem_vonNeumann (hκ : κ.IsInaccessible) {x : ZFSet.{u}} (hx : x ∈ vonNeumann κ.ord)
    (f : ↥x → ZFSet.{u}) (hf : ∀ i, f i ∈ vonNeumann κ.ord) :
    ZFSet.range f ∈ vonNeumann κ.ord := by
  rw [ZFSet.mem_vonNeumann, ZFSet.rank_range]
  have he : (⨆ i : ↥x, succ (rank (f i)))
      = ⨆ j : Shrink.{u} ↥x, succ (rank (f ((equivShrink _).symm j))) :=
    (Equiv.iSup_comp (g := fun i : ↥x => succ (rank (f i)))
      (equivShrink _).symm).symm
  rw [he]
  refine Ordinal.iSup_lt_ord (f := fun j => succ (rank (f ((equivShrink _).symm j)))) ?_ ?_
  · rw [hκ.isRegular.cof_eq]
    exact card_lt_of_mem_vonNeumann hκ hx
  · intro j
    exact (isSuccLimit_ord hκ).succ_lt (ZFSet.mem_vonNeumann.mp (hf _))

/-! ## The first-order language of set theory -/

/-- Relation symbols for the language of set theory: a single binary membership relation. -/
inductive memRel : ℕ → Type
  | mem : memRel 2
  deriving DecidableEq

/-- The first-order language of set theory: one binary relation symbol, for `∈`. -/
def LSet : Language := ⟨fun _ => Empty, memRel⟩

/-- Any `ZFSet` is an `LSet`-structure, with the relation symbol interpreted as membership. -/
instance zfStructure (A : ZFSet.{u}) : LSet.Structure A where
  funMap {_} f := Empty.elim f
  RelMap {n} r := match n, r with
    | 2, .mem => fun v => ((v 0 : A) : ZFSet) ∈ ((v 1 : A) : ZFSet)

/-- `t₁ ∈ t₂` as a bounded formula of `LSet`. -/
def memF {α : Type} {n : ℕ} (t₁ t₂ : LSet.Term (α ⊕ (Fin n))) : LSet.BoundedFormula α n :=
  Relations.boundedFormula₂ memRel.mem t₁ t₂

@[simp] theorem realize_memF {A : ZFSet.{u}} {α : Type} {n : ℕ}
    {t₁ t₂ : LSet.Term (α ⊕ (Fin n))} {v : α → A} {xs : Fin n → A} :
    (memF t₁ t₂).Realize v xs ↔
      ((t₁.realize (Sum.elim v xs) : A) : ZFSet) ∈ ((t₂.realize (Sum.elim v xs) : A) : ZFSet) :=
  BoundedFormula.realize_rel₂

/-! ## The axioms of ZFC -/

/-- Extensionality: two sets with the same elements are equal. -/
def extAx : LSet.Sentence :=
  ∀' ∀' ((∀' ((memF &2 &0) ⇔ (memF &2 &1))) ⟹ (&0 =' &1))

/-- Empty set: there is a set with no elements. -/
def emptyAx : LSet.Sentence := ∃' ∀' (∼ (memF &1 &0))

/-- Pairing: for all `x`, `y` there is a set whose elements are exactly `x` and `y`. -/
def pairAx : LSet.Sentence :=
  ∀' ∀' ∃' ∀' ((memF &3 &2) ⇔ ((&3 =' &0) ⊔ (&3 =' &1)))

/-- Union: for all `x` there is a set whose elements are the elements of elements of `x`. -/
def unionAx : LSet.Sentence :=
  ∀' ∃' ∀' ((memF &2 &1) ⇔ (∃' ((memF &3 &0) ⊓ (memF &2 &3))))

/-- Power set: for all `x` there is a set whose elements are exactly the subsets of `x`. -/
def powerAx : LSet.Sentence :=
  ∀' ∃' ∀' ((memF &2 &1) ⇔ (∀' ((memF &3 &2) ⟹ (memF &3 &0))))

/-- Infinity: there is a set containing the empty set and closed under `y ↦ y ∪ {y}`. -/
def infinityAx : LSet.Sentence :=
  ∃' ((∃' ((memF &1 &0) ⊓ (∀' (∼ (memF &2 &1))))) ⊓
    (∀' ((memF &1 &0) ⟹ (∃' ((memF &2 &0) ⊓
      (∀' ((memF &3 &2) ⇔ ((memF &3 &1) ⊔ (&3 =' &1)))))))))

/-- Foundation: every nonempty set has an `∈`-minimal element. -/
def foundationAx : LSet.Sentence :=
  ∀' ((∃' (memF &1 &0)) ⟹ (∃' ((memF &1 &0) ⊓ (∀' ((memF &2 &0) ⟹ (∼ (memF &2 &1)))))))

/-- Nonemptiness hypothesis in the axiom of choice. -/
def choiceHyp1 : LSet.BoundedFormula Empty 1 :=
  ∀' ((memF &1 &0) ⟹ (∃' (memF &2 &1)))

/-- Pairwise disjointness hypothesis in the axiom of choice. -/
def choiceHyp2 : LSet.BoundedFormula Empty 1 :=
  ∀' ∀' ((memF &1 &0) ⟹ ((memF &2 &0) ⟹
    ((∃' ((memF &3 &1) ⊓ (memF &3 &2))) ⟹ (&1 =' &2))))

/-- Conclusion of the axiom of choice: existence of a transversal. -/
def choiceConcl : LSet.BoundedFormula Empty 1 :=
  ∃' (∀' ((memF &2 &0) ⟹ (∃' ((memF &3 &2) ⊓ ((memF &3 &1) ⊓
    (∀' (((memF &4 &2) ⊓ (memF &4 &1)) ⟹ (&4 =' &3))))))))

/-- Choice, in Zermelo's form: any set of pairwise disjoint nonempty sets admits a set meeting
each of its elements in exactly one point. -/
def choiceAx : LSet.Sentence :=
  ∀' (choiceHyp1 ⟹ (choiceHyp2 ⟹ choiceConcl))

/-- The instance of the separation schema for a formula `φ` with `k` parameters and one further
free variable. -/
noncomputable def sepAx (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 1)) : LSet.Sentence :=
  Formula.iAlls (β := Fin k) (Formula.relabel Sum.inr
    (∀' ∃' ∀' ((memF &2 &1) ⇔ ((memF &2 &0) ⊓
      (BoundedFormula.relabel (k := 0)
        (Sum.elim (fun a => Sum.inl a) (fun _ => Sum.inr 2) : Fin k ⊕ Fin 1 → Fin k ⊕ Fin 3) φ)))))

/-- The functionality hypothesis in the replacement schema. -/
def repHyp (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 2)) : LSet.BoundedFormula (Fin k) 1 :=
  ∀' ∀' ∀' ((memF &1 &0) ⟹
    ((BoundedFormula.relabel (k := 0)
        (Sum.elim (fun a => Sum.inl a) ![Sum.inr 1, Sum.inr 2] : Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ) ⟹
      ((BoundedFormula.relabel (k := 0)
        (Sum.elim (fun a => Sum.inl a) ![Sum.inr 1, Sum.inr 3] : Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ) ⟹
        (&2 =' &3))))

/-- The conclusion of the replacement schema: the image is a set. -/
def repConcl (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 2)) : LSet.BoundedFormula (Fin k) 1 :=
  ∃' ∀' ((memF &2 &1) ⇔ (∃' ((memF &3 &0) ⊓
    (BoundedFormula.relabel (k := 0)
      (Sum.elim (fun a => Sum.inl a) ![Sum.inr 3, Sum.inr 2] : Fin k ⊕ Fin 2 → Fin k ⊕ Fin 4) φ))))

/-- The instance of the replacement schema for a formula `φ` with `k` parameters and two further
free variables. -/
noncomputable def repAx (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 2)) : LSet.Sentence :=
  Formula.iAlls (β := Fin k) (Formula.relabel Sum.inr (∀' (repHyp k φ ⟹ repConcl k φ)))

/-- The first-order theory ZFC, in the language with a single binary relation symbol. -/
def ZFC : LSet.Theory :=
  {extAx, emptyAx, pairAx, unionAx, powerAx, infinityAx, foundationAx, choiceAx}
    ∪ (Set.range fun p : (k : ℕ) × LSet.Formula (Fin k ⊕ Fin 1) => sepAx p.1 p.2)
    ∪ (Set.range fun p : (k : ℕ) × LSet.Formula (Fin k ⊕ Fin 2) => repAx p.1 p.2)

/-! ## Auxiliary simplification lemmas for realization -/

@[simp] theorem comp_elim_one {M : Type*} {k n : ℕ} (v : Fin k → M) (xs : Fin n → M) (j : Fin n) :
    (Sum.elim v xs ∘ Sum.elim (fun a => Sum.inl a) (fun _ : Fin 1 => Sum.inr j))
      = Sum.elim v (fun _ => xs j) := by
  funext x; cases x <;> simp

@[simp] theorem comp_elim_two_default {M : Type*} {k n : ℕ} (v : Fin k → M) (xs : Fin n → M)
    (i j : Fin n) :
    (Sum.elim v xs ∘ Sum.elim (fun a => Sum.inl a)
      (Matrix.vecCons (Sum.inr i) (Matrix.vecCons (Sum.inr j) default) : Fin 2 → _))
      = Sum.elim v ![xs i, xs j] := by
  funext x
  cases x with
  | inl a => simp
  | inr y => fin_cases y <;> simp

@[simp] theorem comp_elim_two {M : Type*} {k n : ℕ} (v : Fin k → M) (xs : Fin n → M) (i j : Fin n) :
    (Sum.elim v xs ∘ Sum.elim (fun a => Sum.inl a) (![Sum.inr i, Sum.inr j] : Fin 2 → _))
      = Sum.elim v ![xs i, xs j] := by
  funext x
  cases x with
  | inl a => simp
  | inr y => fin_cases y <;> simp

/-- Reduce the realization of a sentence in a `ZFSet`-structure to a statement about `ZFSet`s. -/
macro "realize_simp" : tactic =>
  `(tactic| ((simp only [Sentence.Realize, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_ex, BoundedFormula.realize_imp, BoundedFormula.realize_iff,
      BoundedFormula.realize_not, BoundedFormula.realize_inf, BoundedFormula.realize_sup,
      BoundedFormula.realize_bdEqual, realize_memF, Term.realize_var, Function.comp_apply,
      Sum.elim_inr, Sum.elim_inl, Fin.snoc, Formula.realize_iAlls, Formula.realize_relabel,
      BoundedFormula.realize_relabel, Fin.castAdd_zero, Fin.cast_refl, id_eq,
      comp_elim_one, comp_elim_two, Unique.eq_default]); norm_num))

/-! ## Transitive sets with the right closure properties model ZFC -/

variable {A : ZFSet.{u}}

theorem models_extAx (hA : A.IsTransitive) : (A : Type (u+1)) ⊨ extAx := by
  rw [extAx]; realize_simp
  intro a ha b hb h
  apply ZFSet.ext
  intro z
  exact ⟨fun hz => (h z (hA a ha hz)).1 hz, fun hz => (h z (hA b hb hz)).2 hz⟩

theorem models_emptyAx (h : (∅ : ZFSet.{u}) ∈ A) : (A : Type (u+1)) ⊨ emptyAx := by
  rw [emptyAx]; realize_simp
  exact ⟨∅, h, fun y _ => ZFSet.notMem_empty y⟩

theorem models_pairAx (hpair : ∀ x ∈ A, ∀ y ∈ A, ({x, y} : ZFSet) ∈ A) :
    (A : Type (u+1)) ⊨ pairAx := by
  rw [pairAx]; realize_simp
  intro a ha b hb
  refine ⟨{a, b}, hpair a ha b hb, fun w _ => ?_⟩
  simp

theorem models_unionAx (hA : A.IsTransitive) (hun : ∀ x ∈ A, (⋃₀ x) ∈ A) :
    (A : Type (u+1)) ⊨ unionAx := by
  rw [unionAx]; realize_simp
  intro a ha
  refine ⟨⋃₀ a, hun a ha, fun w _ => ?_⟩
  rw [ZFSet.mem_sUnion]
  exact ⟨fun ⟨y, hy, hwy⟩ => ⟨y, hy, hA a ha hy, hwy⟩, fun ⟨y, hy, _, hwy⟩ => ⟨y, hy, hwy⟩⟩

theorem models_powerAx (hA : A.IsTransitive) (hpow : ∀ x ∈ A, x.powerset ∈ A) :
    (A : Type (u+1)) ⊨ powerAx := by
  rw [powerAx]; realize_simp
  intro a ha
  refine ⟨a.powerset, hpow a ha, fun w hw => ?_⟩
  rw [ZFSet.mem_powerset]
  exact ⟨fun hsub y _ hyw => hsub hyw, fun h y hyw => h y (hA w hw hyw) hyw⟩

theorem models_infinityAx (hA : A.IsTransitive) (hom : ZFSet.omega.{u} ∈ A) :
    (A : Type (u+1)) ⊨ infinityAx := by
  rw [infinityAx]; realize_simp
  refine ⟨ZFSet.omega, ⟨∅, ZFSet.omega_zero, hA _ hom ZFSet.omega_zero,
    fun w _ => ZFSet.notMem_empty w⟩, hom, ?_⟩
  intro y _ hyo
  refine ⟨insert y y, ZFSet.omega_succ hyo, hA _ hom (ZFSet.omega_succ hyo), fun w _ => ?_⟩
  rw [ZFSet.mem_insert_iff]
  tauto

theorem models_foundationAx (hA : A.IsTransitive) : (A : Type (u+1)) ⊨ foundationAx := by
  rw [foundationAx]; realize_simp
  intro a ha x _ hxa
  have hne : a ≠ ∅ := by
    intro h
    rw [h] at hxa
    exact ZFSet.notMem_empty x hxa
  obtain ⟨y, hy, hint⟩ := ZFSet.regularity a hne
  refine ⟨y, hy, hA a ha hy, fun c _ hca hcy => ?_⟩
  have hmem : c ∈ a ∩ y := ZFSet.mem_inter.mpr ⟨hca, hcy⟩
  rw [hint] at hmem
  exact ZFSet.notMem_empty c hmem

theorem models_choiceAx (hA : A.IsTransitive)
    (hrange : ∀ x ∈ A, ∀ f : ↥x → ZFSet.{u}, (∀ i, f i ∈ A) → ZFSet.range f ∈ A) :
    (A : Type (u+1)) ⊨ choiceAx := by
  rw [choiceAx, choiceHyp1, choiceHyp2, choiceConcl]; realize_simp
  intro a ha h1 h2
  classical
  have hchoice : ∀ i : ↥a, ∃ w, w ∈ (i : ZFSet) := by
    intro i
    obtain ⟨w, _, hw⟩ := h1 i (hA a ha i.2) i.2
    exact ⟨w, hw⟩
  set f : ↥a → ZFSet.{u} := fun i => (hchoice i).choose with hf
  have hfmem : ∀ i : ↥a, f i ∈ (i : ZFSet) := fun i => (hchoice i).choose_spec
  have hfA : ∀ i : ↥a, f i ∈ A := fun i => hA _ (hA a ha i.2) (hfmem i)
  refine ⟨ZFSet.range f, hrange a ha f hfA, ?_⟩
  intro y hy hya
  refine ⟨f ⟨y, hya⟩, hfmem ⟨y, hya⟩, ZFSet.mem_range_self _, hfA _, ?_⟩
  intro w _ hwy hwr
  obtain ⟨j, hj⟩ := ZFSet.mem_range.mp hwr
  have hjy : (j : ZFSet) = y :=
    h2 j (hA a ha j.2) y hy j.2 hya (f j) (hfmem j) (hfA j) (hj ▸ hwy)
  have : j = ⟨y, hya⟩ := Subtype.ext hjy
  rw [← hj, this]

theorem models_sepAx (hsep : ∀ p : ZFSet.{u} → Prop, ∀ x ∈ A, ZFSet.sep p x ∈ A)
    (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 1)) : (A : Type (u+1)) ⊨ sepAx k φ := by
  rw [sepAx]; realize_simp; realize_simp
  intro i x hx
  classical
  refine ⟨ZFSet.sep (fun y => ∃ h : y ∈ A, φ.Realize (Sum.elim i fun _ => ⟨y, h⟩)) x,
    hsep _ x hx, fun w hw => ?_⟩
  rw [ZFSet.mem_sep]
  exact and_congr_right fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨hw, h⟩⟩

theorem models_repAx (h0 : (∅ : ZFSet.{u}) ∈ A)
    (hsep : ∀ p : ZFSet.{u} → Prop, ∀ x ∈ A, ZFSet.sep p x ∈ A)
    (hrange : ∀ x ∈ A, ∀ f : ↥x → ZFSet.{u}, (∀ i, f i ∈ A) → ZFSet.range f ∈ A)
    (k : ℕ) (φ : LSet.Formula (Fin k ⊕ Fin 2)) : (A : Type (u+1)) ⊨ repAx k φ := by
  rw [repAx, repHyp, repConcl]; realize_simp; realize_simp
  intro i x hx hfun
  classical
  set P : ZFSet.{u} → ZFSet.{u} → Prop := fun w v =>
    ∃ hw : w ∈ A, ∃ hv : v ∈ A, φ.Realize (Sum.elim i ![⟨w, hw⟩, ⟨v, hv⟩]) with hP
  have huniq : ∀ w ∈ x, ∀ v₁ v₂, P w v₁ → P w v₂ → v₁ = v₂ := by
    rintro w hw v₁ v₂ ⟨hwA, hv₁, h₁⟩ ⟨hwA', hv₂, h₂⟩
    exact hfun w hwA v₁ hv₁ v₂ hv₂ hw h₁ h₂
  set f : ↥x → ZFSet.{u} := fun j => if h : ∃ v, P (j : ZFSet) v then h.choose else ∅ with hf
  have hfA : ∀ j : ↥x, f j ∈ A := by
    intro j
    rw [hf]
    by_cases h : ∃ v, P (j : ZFSet) v
    · simp only [h, dif_pos]
      obtain ⟨_, hv, _⟩ := h.choose_spec
      exact hv
    · simpa [h] using h0
  refine ⟨ZFSet.sep (fun v => ∃ w ∈ x, P w v) (ZFSet.range f), hsep _ _ (hrange x hx f hfA),
    fun v hv => ?_⟩
  rw [ZFSet.mem_sep]
  constructor
  · rintro ⟨-, w, hwx, hwA, hvA, hφ⟩
    exact ⟨w, hwx, hwA, hφ⟩
  · rintro ⟨w, hwx, hwA, hφ⟩
    have hPwv : P w v := ⟨hwA, hv, hφ⟩
    have hex : ∃ v', P ((⟨w, hwx⟩ : ↥x) : ZFSet) v' := ⟨v, hPwv⟩
    have hfeq : f ⟨w, hwx⟩ = v := by
      have hspec := hex.choose_spec
      have : f ⟨w, hwx⟩ = hex.choose := by rw [hf]; simp only [hex, dif_pos]
      rw [this]
      exact huniq w hwx _ _ hspec hPwv
    exact ⟨hfeq ▸ ZFSet.mem_range_self (⟨w, hwx⟩ : ↥x), w, hwx, hPwv⟩

/-! ## `V_κ` models ZFC for `κ` inaccessible -/

theorem vonNeumann_models_ZFC (hκ : κ.IsInaccessible) :
    (vonNeumann κ.ord : Type (u+1)) ⊨ ZFC := by
  have hA : (vonNeumann κ.ord).IsTransitive := isTransitive_vonNeumann _
  have hsep : ∀ p : ZFSet.{u} → Prop, ∀ x ∈ vonNeumann κ.ord, ZFSet.sep p x ∈ vonNeumann κ.ord :=
    fun p x hx => sep_mem_vonNeumann p hx
  have hrange : ∀ x ∈ vonNeumann κ.ord, ∀ f : ↥x → ZFSet.{u},
      (∀ i, f i ∈ vonNeumann κ.ord) → ZFSet.range f ∈ vonNeumann κ.ord :=
    fun x hx f hf => range_mem_vonNeumann hκ hx f hf
  refine (Theory.model_iff _).mpr ?_
  rintro s ((hs | ⟨⟨k, φ⟩, rfl⟩) | ⟨⟨k, φ⟩, rfl⟩)
  · rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact models_extAx hA
    · exact models_emptyAx (empty_mem_vonNeumann hκ)
    · exact models_pairAx fun x hx y hy => pair_mem_vonNeumann hκ hx hy
    · exact models_unionAx hA fun x hx => sUnion_mem_vonNeumann hx
    · exact models_powerAx hA fun x hx => powerset_mem_vonNeumann hκ hx
    · exact models_infinityAx hA (omega_mem_vonNeumann hκ)
    · exact models_foundationAx hA
    · exact models_choiceAx hA hrange
  · exact models_sepAx hsep k φ
  · exact models_repAx (empty_mem_vonNeumann hκ) hsep hrange k φ

/-! ## Main results -/

/-- **An inaccessible cardinal yields a model of ZFC.**  If `κ` is a (strongly) inaccessible
cardinal, then the level `V_κ` of the von Neumann hierarchy is a model of the first-order theory
`ZFC`; in particular `ZFC` is consistent (satisfiable). -/
theorem inaccessible_implies_ConZFC (hκ : κ.IsInaccessible) : ZFC.IsSatisfiable := by
  haveI : Nonempty (vonNeumann κ.ord : Type (u+1)) := ⟨⟨∅, empty_mem_vonNeumann hκ⟩⟩
  haveI := vonNeumann_models_ZFC hκ
  exact Theory.Model.isSatisfiable (vonNeumann κ.ord : Type (u+1))

/-- The reduction `Con(ZFC + inaccessible) → Con(ZFC)`: any theory extending `ZFC` (for instance
`ZFC` together with an axiom asserting the existence of an inaccessible cardinal) is consistent
only if `ZFC` is. -/
theorem ConZFC_of_ConZFC_extension {T : LSet.Theory} (hT : ZFC ⊆ T) (h : T.IsSatisfiable) :
    ZFC.IsSatisfiable :=
  h.mono hT

/-- Lean's ambient type theory proves the existence of an inaccessible cardinal (the cardinality
of a universe), so the above gives an unconditional proof that `ZFC` is satisfiable. -/
theorem ConZFC : ZFC.IsSatisfiable :=
  inaccessible_implies_ConZFC Cardinal.IsInaccessible.univ.{0, 1}

/-! ## Nontriviality checks

These two lemmas confirm that the formalized theory has genuine content: it is not satisfied by
arbitrary transitive sets.  Pairing already fails in `{∅}`, and Infinity fails in the set `V_ω` of
hereditarily finite sets (which does satisfy all the other axioms). -/

theorem not_models_pairAx_singleton : ¬ ((({∅} : ZFSet.{0}) : Type 1) ⊨ pairAx) := by
  rw [pairAx]; realize_simp

theorem not_models_infinityAx_vonNeumann_omega0 :
    ¬ ((vonNeumann Ordinal.omega0.{0} : Type 1) ⊨ infinityAx) := by
  rw [infinityAx]; realize_simp
  intro a e hea _ _ haV
  have htr : (vonNeumann Ordinal.omega0.{0}).IsTransitive := isTransitive_vonNeumann _
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp (ZFSet.mem_vonNeumann.mp haV)
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := by
    cases n with
    | zero =>
      exfalso
      have hlt := ZFSet.rank_lt_of_mem hea
      rw [hn] at hlt
      simp at hlt
    | succ m => exact ⟨m, rfl⟩
  obtain ⟨y, hya, hym⟩ : ∃ y ∈ a, ((m : Ordinal)) ≤ ZFSet.rank y := by
    refine ZFSet.lt_rank_iff.mp ?_
    rw [hn]
    exact_mod_cast Nat.lt_succ_self m
  have hylt : ZFSet.rank y < ((m : Ordinal) + 1) := by
    have hlt := ZFSet.rank_lt_of_mem hya
    rw [hn] at hlt
    exact_mod_cast hlt
  have hyrank : ZFSet.rank y = (m : Ordinal) :=
    le_antisymm (by rwa [← Order.succ_eq_add_one, Order.lt_succ_iff] at hylt) hym
  refine ⟨y, htr a haV hya, hya, ?_⟩
  intro s hsa hsV
  by_contra hcon
  push_neg at hcon
  have hseq : s = insert y y := by
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hw
      have := (hcon w (htr s hsV hw)).1 hw
      tauto
    · intro hw
      have hwV : w ∈ vonNeumann Ordinal.omega0.{0} := by
        rcases hw with rfl | hw
        · exact htr a haV hya
        · exact htr _ (htr a haV hya) hw
      exact (hcon w hwV).2 (by tauto)
  have hrs : ZFSet.rank s = (m : Ordinal) + 1 := by
    rw [hseq, ZFSet.rank_insert, hyrank, max_eq_left (Order.le_succ _), Order.succ_eq_add_one]
  have hlt := ZFSet.rank_lt_of_mem hsa
  rw [hn, hrs] at hlt
  exact absurd hlt (lt_irrefl _)

end Frontier

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

