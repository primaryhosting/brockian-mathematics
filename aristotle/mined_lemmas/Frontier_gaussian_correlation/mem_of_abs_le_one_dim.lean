import Mathlib

/-!
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

/-- The standard (centered, isotropic) Gaussian measure on `ℝ ^ n`, realized as the product of
`n` copies of the standard Gaussian measure on `ℝ`. -/

theorem mem_of_abs_le_one_dim {S : Set (Fin 1 → ℝ)} (hconv : Convex ℝ S)
    (hsymm : ∀ x ∈ S, -x ∈ S) {x y : Fin 1 → ℝ} (hx : x ∈ S) (hxy : |y 0| ≤ |x 0|) : y ∈ S := by
  by_cases hx0 : x 0 = 0
  · have hy0 : y 0 = 0 := by
      have : |y 0| ≤ 0 := by simpa [hx0] using hxy
      simpa using abs_nonpos_iff.mp this
    have hxy' : y = x := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rw [hy0, hx0]
    rwa [hxy']
  · have hc : |y 0 / x 0| ≤ 1 := by
      rw [abs_div]
      rw [div_le_one (abs_pos.mpr hx0)]
      exact hxy
    have hmem := smul_mem_of_abs_le_one hconv hsymm hx hc
    have heq : (y 0 / x 0) • x = y := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    rwa [heq] at hmem

/-- Two origin-symmetric convex subsets of the line are always nested. -/
