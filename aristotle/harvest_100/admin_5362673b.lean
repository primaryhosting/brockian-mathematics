/-
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Classical

namespace Riemann.BaezDuarte

/-- **Gram nonnegativity (clean self-contained case).**
For all reals `a b`, the quadratic form `a ^ 2 - 2 * a * b + b ^ 2` is nonnegative,
since it equals the square `(a - b) ^ 2`.  This is the two-dimensional Gram /
distance nonnegativity underlying the Nyman–Beurling–Baez-Duarte criterion, where
the relevant distance is a sum of such squares. -/
theorem gram_nonneg (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  have h : a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
  rw [h]
  positivity

/-- **General Gram nonnegativity.**
In any real inner product space `V`, for a finite family of vectors `v : Fin n → V`
and coefficients `c : Fin n → ℝ`, the Gram quadratic form
`∑ i, ∑ j, c i * c j * ⟪v i, v j⟫` is nonnegative, being the inner product of
`∑ i, c i • v i` with itself. -/
theorem gram_nonneg_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} (v : Fin n → V) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * inner ℝ (v i) (v j) := by
  have key : ∑ i, ∑ j, c i * c j * inner ℝ (v i) (v j)
      = inner ℝ (∑ i, c i • v i) (∑ j, c j • v j) := by
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_assoc]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [real_inner_comm]
  rw [key]
  exact real_inner_self_nonneg

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

