import Mathlib

/-!
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators RealInnerProductSpace

namespace Riemann.BaezDuarte

/-- The Gram/distance nonnegativity in its clean self-contained shape:
for all real `a`, `b`, `0 ≤ a ^ 2 - 2 * a * b + b ^ 2`, since the expression is `(a - b) ^ 2`.
Closed by Mathlib's `sq_nonneg`. -/
theorem gram_nonneg (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  have h : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
  rw [h]
  exact sq_nonneg (a - b)

/-- The Gram sum of a finite family of vectors in a real inner product space equals the
squared norm of the corresponding linear combination. -/
theorem gram_sum_eq_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (v : Fin n → V) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * ⟪v i, v j⟫ = ‖∑ i, c i • v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, mul_assoc]

/-- Nyman–Beurling / Baez-Duarte finite shape: in any real inner product space, the Gram
quadratic form `∑ i, ∑ j, c i * c j * ⟪v i, v j⟫` of a finite family of vectors is
nonnegative, being the squared norm of `∑ i, c i • v i`. -/
theorem gram_sum_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (v : Fin n → V) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * ⟪v i, v j⟫ := by
  rw [gram_sum_eq_norm_sq]
  exact sq_nonneg _

end Riemann.BaezDuarte

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

