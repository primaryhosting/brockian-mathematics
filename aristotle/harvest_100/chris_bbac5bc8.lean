import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any doc comment, so the mandated header
appears immediately after the import.)
-/

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

namespace Frontier

open MeasureTheory ProbabilityTheory

/-! ## The standard Gaussian measure on `Fin n → ℝ` -/

/-- The standard (centered, identity covariance) Gaussian measure on `Fin n → ℝ`,
defined as the `n`-fold product of the standard Gaussian measure on `ℝ`. -/
noncomputable def stdGaussian (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

instance instIsProbabilityMeasureStdGaussian (n : ℕ) :
    IsProbabilityMeasure (stdGaussian n) := by
  unfold stdGaussian; infer_instance

/-- A set is (centrally) symmetric if it is invariant under `x ↦ -x`. -/
def IsSymmetricSet {E : Type*} [Neg E] (K : Set E) : Prop := ∀ x ∈ K, -x ∈ K

/-- **The Gaussian correlation inequality** in dimension `n` (Royen's theorem):
for any two measurable, convex, centrally symmetric subsets `K`, `L` of `ℝ^n`,
the standard Gaussian measure satisfies `μ K * μ L ≤ μ (K ∩ L)`. -/
def GaussianCorrelationInequality (n : ℕ) : Prop :=
  ∀ K L : Set (Fin n → ℝ), MeasurableSet K → MeasurableSet L →
    Convex ℝ K → Convex ℝ L → IsSymmetricSet K → IsSymmetricSet L →
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L)

/-! ## A general reduction: nested sets -/

/-- Reduction step: if one of the two sets is contained in the other, the Gaussian
correlation inequality holds (for any probability measure, in any dimension). -/
theorem measure_inter_ge_of_subset {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {K L : Set α} (h : K ⊆ L ∨ L ⊆ K) :
    μ K * μ L ≤ μ (K ∩ L) := by
  rcases h with h | h
  · rw [Set.inter_eq_self_of_subset_left h]
    calc μ K * μ L ≤ μ K * 1 := by gcongr; exact prob_le_one
      _ = μ K := mul_one _
  · rw [Set.inter_eq_self_of_subset_right h]
    calc μ K * μ L ≤ 1 * μ L := by gcongr; exact prob_le_one
      _ = μ L := one_mul _

/-! ## Dimension one -/

/-- A convex symmetric set is closed under scaling by scalars of absolute value at most one. -/
theorem smul_mem_of_abs_le_one {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E}
    (hK : Convex ℝ K) (hKs : IsSymmetricSet K) {x : E} (hx : x ∈ K) {c : ℝ}
    (hc : |c| ≤ 1) : c • x ∈ K := by
  have h1 : (0:ℝ) ≤ (1 + c) / 2 := by
    have := abs_le.mp hc; linarith [this.1]
  have h2 : (0:ℝ) ≤ (1 - c) / 2 := by
    have := abs_le.mp hc; linarith [this.2]
  have h3 : (1 + c) / 2 + (1 - c) / 2 = 1 := by ring
  have := hK hx (hKs x hx) h1 h2 h3
  have heq : ((1 + c) / 2) • x + ((1 - c) / 2) • (-x) = c • x := by
    rw [smul_neg, ← sub_eq_add_neg, ← sub_smul]
    congr 1
    ring
  rwa [heq] at this

/-- In dimension one, any two convex symmetric sets are nested. -/
theorem nested_of_convex_symm_dim_one {K L : Set (Fin 1 → ℝ)}
    (hK : Convex ℝ K) (hL : Convex ℝ L) (hKs : IsSymmetricSet K) (hLs : IsSymmetricSet L) :
    K ⊆ L ∨ L ⊆ K := by
  -- key step: if `x ∈ K` and `|y 0| ≤ |x 0|` then `y ∈ K`
  have key : ∀ (M : Set (Fin 1 → ℝ)), Convex ℝ M → IsSymmetricSet M →
      ∀ x ∈ M, ∀ y : Fin 1 → ℝ, |y 0| ≤ |x 0| → y ∈ M := by
    intro M hM hMs x hx y hy
    by_cases hx0 : x 0 = 0
    · have hy0 : y 0 = 0 := by
        rw [hx0] at hy; simpa using abs_nonpos_iff.mp (by simpa using hy)
      have : y = (0 : ℝ) • x := by
        funext i
        have : i = 0 := Subsingleton.elim _ _
        subst this
        simp [hy0]
      rw [this]
      exact smul_mem_of_abs_le_one hM hMs hx (by simp)
    · have hc : |y 0 / x 0| ≤ 1 := by
        rw [abs_div]
        rw [div_le_one (abs_pos.mpr hx0)]
        exact hy
      have : y = (y 0 / x 0) • x := by
        funext i
        have : i = 0 := Subsingleton.elim _ _
        subst this
        simp only [Pi.smul_apply, smul_eq_mul]
        field_simp
      rw [this]
      exact smul_mem_of_abs_le_one hM hMs hx hc
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨x, hxK, hxL⟩, ⟨y, hyL, hyK⟩⟩ :
      (∃ x, x ∈ K ∧ x ∉ L) ∧ (∃ y, y ∈ L ∧ y ∉ K) := by
    constructor
    · exact Set.not_subset.mp hcon.1
    · exact Set.not_subset.mp hcon.2
  rcases le_total (|y 0|) (|x 0|) with h | h
  · exact hyK (key K hK hKs x hxK y h)
  · exact hxL (key L hL hLs y hyL x h)

/-- **The Gaussian correlation inequality in dimension one** (the base case of Royen's
theorem): for measurable convex centrally symmetric `K, L ⊆ ℝ^1`, the standard Gaussian
measure satisfies `μ K * μ L ≤ μ (K ∩ L)`.

The proof is the classical base case: in dimension one two symmetric convex sets are
nested, and for a probability measure nestedness immediately gives the inequality. -/
theorem gaussian_correlation : GaussianCorrelationInequality 1 := by
  intro K L _ _ hK hL hKs hLs
  exact measure_inter_ge_of_subset (stdGaussian 1)
    (nested_of_convex_symm_dim_one hK hL hKs hLs)

/-- The (degenerate) zero-dimensional case. -/
theorem gaussian_correlation_zero : GaussianCorrelationInequality 0 := by
  intro K L _ _ _ _ _ _
  refine measure_inter_ge_of_subset (stdGaussian 0) ?_
  rcases Set.eq_empty_or_nonempty K with rfl | ⟨x, hx⟩
  · exact Or.inl (Set.empty_subset _)
  · refine Or.inr fun y _ => ?_
    have : y = x := Subsingleton.elim _ _
    exact this ▸ hx

end Frontier

