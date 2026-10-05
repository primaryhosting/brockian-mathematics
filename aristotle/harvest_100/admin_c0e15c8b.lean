/-
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
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

namespace Riemann
namespace BaezDuarte

/-- **Gram nonnegativity, general form.** In any real inner product space `V`, for a finite
family of vectors `v : Fin n → V` and coefficients `c : Fin n → ℝ`, the associated Gram
quadratic form `∑ i, ∑ j, c i * c j * ⟪v i, v j⟫` is nonnegative: it equals the squared norm
of `∑ i, c i • v i`. -/
theorem gram_form_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (v : Fin n → V) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (inner ℝ (v i) (v j) : ℝ) := by
  have h : ∑ i, ∑ j, c i * c j * (inner ℝ (v i) (v j) : ℝ)
      = (inner ℝ (∑ i, c i • v i) (∑ j, c j • v j) : ℝ) := by
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_smul_right]
    ring
  rw [h]
  exact real_inner_self_nonneg

/-- **Gram nonnegativity (clean self-contained case).** For all real `a` and `b`,
`0 ≤ a^2 - 2*a*b + b^2`, i.e. the Gram/distance form `‖a - b‖^2` is nonnegative.
The Baez-Duarte / Nyman-Beurling distance is a sum of such squares. -/
theorem gram_nonneg : ∀ a b : ℝ, 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  intro a b
  nlinarith [sq_nonneg (a - b)]

end BaezDuarte
end Riemann

