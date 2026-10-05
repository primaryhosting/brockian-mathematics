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

open MeasureTheory

/-! ## The standard Gaussian measure and the statement of the inequality -/

/-- The standard Gaussian (probability) measure on `ℝ ^ n`, realised as the `n`-fold product
of the one-dimensional standard Gaussian `N(0,1)`. -/

theorem gaussian_correlation_dim_zero : GaussianCorrelationStatement 0 := by
  intro K L _ _ _ _
  rcases Set.eq_empty_or_nonempty K with rfl | ⟨x, hx⟩
  · simp
  rcases Set.eq_empty_or_nonempty L with rfl | ⟨y, hy⟩
  · simp
  have hxy : x = y := Subsingleton.elim _ _
  have hKL : K ∩ L = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    have hzx : z = x := Subsingleton.elim _ _
    exact ⟨hzx ▸ hx, hzx ▸ hxy ▸ hy⟩
  rw [hKL, measure_univ]
  calc stdGaussian 0 K * stdGaussian 0 L ≤ 1 * 1 :=
        mul_le_mul' prob_le_one prob_le_one
    _ = 1 := mul_one 1

/-- **Gaussian correlation inequality for boxes, in every dimension.**
If `K = ∏ i, A i` and `L = ∏ i, B i` are products of symmetric convex subsets of the line
(hence themselves symmetric convex subsets of `ℝ ^ n`), then `γ(K) · γ(L) ≤ γ(K ∩ L)`. -/
