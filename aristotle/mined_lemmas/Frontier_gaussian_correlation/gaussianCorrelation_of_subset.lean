/-
# Gaussian Correlation
Category: Frontier — Fields Medal Work
Target: Frontier.gaussian_correlation
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

open MeasureTheory ProbabilityTheory

namespace Frontier

/-- The standard Gaussian measure on `ℝ^n`, defined as the `n`-fold product of the
standard Gaussian measure on `ℝ`. -/

theorem gaussianCorrelation_of_subset {n : ℕ} (K L : Set (Fin n → ℝ))
    (h : K ⊆ L ∨ L ⊆ K) :
    stdGaussian n K * stdGaussian n L ≤ stdGaussian n (K ∩ L) := by
  rcases h with h | h
  · have hKL : K ∩ L = K := Set.inter_eq_self_of_subset_left h
    calc stdGaussian n K * stdGaussian n L ≤ stdGaussian n K * 1 :=
          mul_le_mul_left' prob_le_one _
      _ = stdGaussian n (K ∩ L) := by rw [mul_one, hKL]
  · have hKL : K ∩ L = L := Set.inter_eq_self_of_subset_right h
    calc stdGaussian n K * stdGaussian n L ≤ 1 * stdGaussian n L :=
          mul_le_mul_right' prob_le_one _
      _ = stdGaussian n (K ∩ L) := by rw [one_mul, hKL]

/-! ### The one-dimensional case -/

/-- A symmetric convex subset of `ℝ` contains every point that is no further from the
origin than one of its points. -/
