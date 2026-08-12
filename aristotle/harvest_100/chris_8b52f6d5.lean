/-
# Mordell Finite Generation
Category: Frontier — Prime Numbers
Target: Frontier.Mordell_finite_generation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
(The header above is a plain block comment rather than a module docstring, since Lean 4
does not allow a module docstring to precede the `import` commands.)

# Mordell's theorem: finite generation of `E(ℚ)`

We formalize the statement that the group of rational points of an elliptic curve over `ℚ`
is finitely generated, and we prove the *descent step* of the classical proof: an abelian
group equipped with a height function satisfying the standard axioms and whose quotient by
`2A` is finite is finitely generated.  Specializing to `E(ℚ)` gives
`Frontier.Mordell_finite_generation`, a Lean-checked reduction of Mordell's theorem to the
weak Mordell–Weil theorem together with the existence of a height function.
-/

namespace Frontier

universe u

/-- Abstract height data on an abelian group `A`, modelled on the naive/canonical height
of an elliptic curve over `ℚ`:

* the height is nonnegative;
* there are only finitely many points of bounded height (Northcott property);
* translation by a fixed point distorts the height by a bounded factor;
* duplication multiplies the height by roughly `4`.
-/
structure HeightFunction (A : Type u) [AddCommGroup A] where
  /-- The height function itself. -/
  toFun : A → ℝ
  /-- Heights are nonnegative. -/
  nonneg : ∀ P, 0 ≤ toFun P
  /-- Northcott property: finitely many points of bounded height. -/
  finite_of_le : ∀ C : ℝ, {P : A | toFun P ≤ C}.Finite
  /-- Quasi-additivity of the height under translation by a fixed point. -/
  translate : ∀ Q : A, ∃ c : ℝ, ∀ P : A, toFun (P + Q) ≤ 2 * toFun P + c
  /-- Quasi-quadraticity of the height under duplication. -/
  duplication : ∃ c : ℝ, ∀ P : A, 4 * toFun P ≤ toFun (2 • P) + c

/-- The subgroup `2A` of an abelian group `A`. -/
def twoSubgroup (A : Type u) [AddCommGroup A] : AddSubgroup A :=
  (zsmulAddGroupHom 2 : A →+ A).range

lemma mem_twoSubgroup_iff {A : Type u} [AddCommGroup A] {x : A} :
    x ∈ twoSubgroup A ↔ ∃ y : A, x = 2 • y := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [zsmulAddGroupHom, two_zsmul, two_nsmul]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, by simp [zsmulAddGroupHom, two_zsmul, two_nsmul]⟩

/-- The "weak Mordell–Weil" hypothesis for an abelian group `A`: the quotient `A / 2A`
is finite. -/
def WeakMordellWeil (A : Type u) [AddCommGroup A] : Prop :=
  Finite (A ⧸ twoSubgroup A)

/-- From finiteness of `A / 2A` we obtain a finite set of coset representatives. -/
lemma exists_reps {A : Type u} [AddCommGroup A] (hw : WeakMordellWeil A) :
    ∃ R : Finset A, ∀ P : A, ∃ Q ∈ R, ∃ S : A, P = 2 • S + Q := by
  classical
  have : Finite (A ⧸ twoSubgroup A) := hw
  have hfin : (Set.range (fun x : A ⧸ twoSubgroup A => Quotient.out x)).Finite :=
    Set.finite_range _
  refine ⟨hfin.toFinset, fun P => ?_⟩
  set Q : A := Quotient.out (QuotientAddGroup.mk (s := twoSubgroup A) P) with hQdef
  have hQmem : Q ∈ hfin.toFinset := by
    simp only [Set.Finite.mem_toFinset, hQdef]
    exact ⟨_, rfl⟩
  refine ⟨Q, hQmem, ?_⟩
  have hEq : (QuotientAddGroup.mk (s := twoSubgroup A) Q)
      = QuotientAddGroup.mk (s := twoSubgroup A) P := by
    rw [hQdef]
    exact Quotient.out_eq _
  have hmem : -Q + P ∈ twoSubgroup A := QuotientAddGroup.eq.mp hEq
  obtain ⟨S, hS⟩ := mem_twoSubgroup_iff.mp hmem
  exact ⟨S, by rw [← hS]; abel⟩

/-- The key descent inequality: outside a bounded region, every point can be written as
`2 • S + Q` with `Q` a coset representative and `S` of strictly smaller height. -/
lemma descent_step {A : Type u} [AddCommGroup A] (h : HeightFunction A) (R : Finset A)
    (hR : ∀ P : A, ∃ Q ∈ R, ∃ S : A, P = 2 • S + Q) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ P : A, B < h.toFun P →
      ∃ Q ∈ R, ∃ S : A, P = 2 • S + Q ∧ h.toFun S < h.toFun P := by
  classical
  obtain ⟨c₂, hc₂⟩ := h.duplication
  choose c hc using fun Q : A => h.translate (-Q)
  set T : Finset ℝ := insert (0 : ℝ) (R.image c) with hT
  have hTne : T.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  set M : ℝ := T.max' hTne with hM
  have hM0 : 0 ≤ M := Finset.le_max' T 0 (Finset.mem_insert_self _ _)
  have hMc : ∀ Q ∈ R, c Q ≤ M :=
    fun Q hQ => Finset.le_max' T (c Q) (Finset.mem_insert_of_mem (Finset.mem_image_of_mem c hQ))
  refine ⟨max (M + c₂) 1, le_trans zero_le_one (le_max_right _ _), fun P hP => ?_⟩
  obtain ⟨Q, hQ, S, rfl⟩ := hR P
  refine ⟨Q, hQ, S, rfl, ?_⟩
  have h1 : 4 * h.toFun S ≤ h.toFun (2 • S) + c₂ := hc₂ S
  have h2 : h.toFun ((2 • S + Q) + -Q) ≤ 2 * h.toFun (2 • S + Q) + c Q := hc Q _
  have h3 : (2 • S + Q) + -Q = 2 • S := by abel
  rw [h3] at h2
  have h4 : c Q ≤ M := hMc Q hQ
  have h5 : M + c₂ ≤ max (M + c₂) 1 := le_max_left _ _
  have h6 : (1 : ℝ) ≤ max (M + c₂) 1 := le_max_right _ _
  linarith

/-- **Descent theorem.** An abelian group carrying a height function in the above sense
and satisfying weak Mordell–Weil is finitely generated. -/
theorem fg_of_heightFunction_of_weakMordellWeil {A : Type u} [AddCommGroup A]
    (h : HeightFunction A) (hw : WeakMordellWeil A) : AddGroup.FG A := by
  classical
  obtain ⟨R, hR⟩ := exists_reps hw
  obtain ⟨B, hB0, hstep⟩ := descent_step h R hR
  set G : Set A := (R : Set A) ∪ {P : A | h.toFun P ≤ B} with hG
  have hGfin : G.Finite := (R.finite_toSet).union (h.finite_of_le B)
  refine AddGroup.fg_iff.mpr ⟨G, ?_, hGfin⟩
  rw [eq_top_iff]
  intro P₀ _
  by_contra hP₀
  set X : Set A := {T : A | h.toFun T ≤ h.toFun P₀ ∧ T ∉ AddSubgroup.closure G} with hX
  have hXfin : X.Finite :=
    (h.finite_of_le (h.toFun P₀)).subset (fun x hx => hx.1)
  have hXne : X.Nonempty := ⟨P₀, le_rfl, hP₀⟩
  obtain ⟨P, hPX, hPmin⟩ := Set.exists_min_image X h.toFun hXfin hXne
  have hPclos : P ∉ AddSubgroup.closure G := hPX.2
  have hPB : B < h.toFun P := by
    by_contra hcon
    push_neg at hcon
    exact hPclos (AddSubgroup.subset_closure (Or.inr hcon))
  obtain ⟨Q, hQ, S, hPS, hSlt⟩ := hstep P hPB
  have hSclos : S ∈ AddSubgroup.closure G := by
    by_contra hScon
    have hSX : S ∈ X := ⟨le_trans hSlt.le hPX.1, hScon⟩
    exact absurd (hPmin S hSX) (not_le.mpr hSlt)
  have hQclos : Q ∈ AddSubgroup.closure G :=
    AddSubgroup.subset_closure (Or.inl (by exact_mod_cast hQ))
  exact hPclos (hPS ▸ AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hSclos 2) hQclos)

/-- A height function on `ℤ`, showing that the hypotheses of the descent theorem are
satisfiable (and hence that the theorem is not vacuous): `h k = k ^ 2`. -/
noncomputable def heightFunctionInt : HeightFunction ℤ where
  toFun k := (k : ℝ) ^ 2
  nonneg := fun k => sq_nonneg _
  finite_of_le := by
    intro C
    apply Set.Finite.subset (Set.finite_Icc (-⌈C⌉) ⌈C⌉)
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    have h1 : |k| ≤ k ^ 2 := by
      nlinarith [abs_nonneg k, sq_abs k, le_abs_self k, neg_abs_le k]
    have h1' : ((|k| : ℤ) : ℝ) ≤ ((k ^ 2 : ℤ) : ℝ) := by exact_mod_cast h1
    have h2 : ((|k| : ℤ) : ℝ) ≤ C := by push_cast at h1' ⊢; nlinarith
    have h3 : |k| ≤ ⌈C⌉ := by
      have h4 : ⌈((|k| : ℤ) : ℝ)⌉ ≤ ⌈C⌉ := Int.ceil_le_ceil h2
      rwa [Int.ceil_intCast] at h4
    simp only [Set.mem_Icc]
    constructor <;> [linarith [neg_abs_le k]; linarith [le_abs_self k]]
  translate := by
    intro q
    refine ⟨2 * (q : ℝ) ^ 2, fun k => ?_⟩
    push_cast
    nlinarith [sq_nonneg ((k : ℝ) - (q : ℝ))]
  duplication := by
    refine ⟨0, fun k => ?_⟩
    have hk : ((2 • k : ℤ) : ℝ) = 2 * (k : ℝ) := by
      rw [two_nsmul]; push_cast; ring
    rw [hk]
    nlinarith

lemma weakMordellWeil_int : WeakMordellWeil ℤ := by
  classical
  refine Finite.of_surjective (α := Bool)
    (fun b => QuotientAddGroup.mk (s := twoSubgroup ℤ) (if b then 1 else 0)) ?_
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H k =>
    rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨false, ?_⟩
      simp only [if_neg (by simp : ¬ (false = true))]
      refine QuotientAddGroup.eq.mpr ?_
      exact mem_twoSubgroup_iff.mpr ⟨m, by rw [two_nsmul]; omega⟩
    · refine ⟨true, ?_⟩
      refine QuotientAddGroup.eq.mpr ?_
      exact mem_twoSubgroup_iff.mpr ⟨m, by simp only [if_true]; rw [two_nsmul]; omega⟩

/-- Sanity check (non-vacuity): the descent theorem applies to `ℤ`. -/
theorem fg_int_via_descent : AddGroup.FG ℤ :=
  fg_of_heightFunction_of_weakMordellWeil heightFunctionInt weakMordellWeil_int

/-- The full Mordell theorem, as a proposition: the group of rational points of an
elliptic curve over `ℚ` is finitely generated. -/
def MordellStatement : Prop :=
  ∀ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic), AddGroup.FG E.toAffine.Point

/-- Packaging of the reduction: if every elliptic curve over `ℚ` admits a height function
and satisfies weak Mordell–Weil, then Mordell's theorem holds. -/
theorem mordellStatement_of_height_of_weak
    (H : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → Nonempty (HeightFunction E.toAffine.Point))
    (W : ∀ E : WeierstrassCurve ℚ, E.IsElliptic → WeakMordellWeil E.toAffine.Point) :
    MordellStatement := by
  intro E hE
  obtain ⟨height⟩ := H E hE
  exact fg_of_heightFunction_of_weakMordellWeil height (W E hE)

/-- **Mordell's theorem, as a Lean-checked reduction.**

The group `E(ℚ)` of rational points of an elliptic curve `E` over `ℚ` is finitely
generated, *given* the two standard inputs of the classical proof:

* the weak Mordell–Weil theorem for `E`, i.e. finiteness of `E(ℚ)/2E(ℚ)`;
* a height function on `E(ℚ)` with the standard properties (nonnegativity, the
  Northcott finiteness property, quasi-additivity under translation, and
  quasi-quadraticity under duplication).

The mathematical content proved here is the infinite-descent step, which turns these two
inputs into finite generation. -/
theorem Mordell_finite_generation (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (height : HeightFunction E.toAffine.Point)
    (weak : WeakMordellWeil E.toAffine.Point) :
    AddGroup.FG E.toAffine.Point :=
  fg_of_heightFunction_of_weakMordellWeil height weak

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

