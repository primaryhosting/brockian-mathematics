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
