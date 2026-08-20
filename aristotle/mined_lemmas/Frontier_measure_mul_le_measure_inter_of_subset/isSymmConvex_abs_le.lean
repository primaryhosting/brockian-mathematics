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

set_option grind.warning false

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- A set is *symmetric convex* if it is convex and invariant under `x ↦ -x`. -/

theorem isSymmConvex_abs_le (a : ℝ) : IsSymmConvex {t : ℝ | |t| ≤ a} := by
  constructor
  · intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq] at *
    calc |s • x + t • y| ≤ |s * x| + |t * y| := abs_add_le _ _
      _ = s * |x| + t * |y| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
      _ ≤ s * a + t * a := by gcongr
      _ = a := by rw [← add_mul, hst, one_mul]
  · intro x hx
    simpa using hx

/-- **Parallel slabs.** For a Gaussian measure on a Banach space, the correlation inequality
holds for two symmetric slabs determined by the same continuous linear functional. -/
