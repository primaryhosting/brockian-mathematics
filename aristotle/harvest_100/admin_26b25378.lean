/-!
# Gram Nonneg
Category: Frontier Wave 2 (deeper machinery)
Target: Riemann.BaezDuarte.gram_nonneg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.BaezDuarte

open scoped InnerProductSpace BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gram form of a finite family of vectors in a real inner product space is
nonnegative: it is the squared norm of the corresponding linear combination. -/
theorem gram_sum_eq_norm_sq {n : ℕ} (v : Fin n → V) (c : Fin n → ℝ) :
    ∑ i, ∑ j, c i * c j * (inner (v i) (v j) : ℝ) = ‖∑ i, c i • v i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum, real_inner_smul_left, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right]
  ring

/-- **Gram nonnegativity** (Nyman–Beurling / Baez-Duarte finite shape):
in any real inner product space, for any finite family of vectors `v` and any real
coefficients `c`, the Gram form `∑ i j, c i * c j * ⟪v i, v j⟫` is nonnegative. -/
theorem gram_nonneg {n : ℕ} (v : Fin n → V) (c : Fin n → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * (inner (v i) (v j) : ℝ) := by
  rw [gram_sum_eq_norm_sq]
  positivity

/-- The concrete self-contained case: `0 ≤ a^2 - 2*a*b + b^2`, i.e. the squared
distance `‖a - b‖^2` in the one-dimensional case, which is the basic square whose
sums make up the Baez-Duarte distance. -/
theorem gram_nonneg_two (a b : ℝ) : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- The concrete case is an instance of the general Gram nonnegativity statement,
with `v = ![x, -x]` for a unit vector `x` and coefficients `c = ![a, b]`. -/
theorem gram_nonneg_two_of_gram (a b : ℝ) :
    0 ≤ ∑ i : Fin 2, ∑ j : Fin 2,
      (![a, b] i) * (![a, b] j) * (inner (![(1 : ℝ), -1] i) (![(1 : ℝ), -1] j) : ℝ) :=
  gram_nonneg _ _

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

