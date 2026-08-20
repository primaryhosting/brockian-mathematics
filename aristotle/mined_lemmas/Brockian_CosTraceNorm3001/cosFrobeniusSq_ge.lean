import Mathlib
import RequestProject.Brockian.CosTraceNorm3001

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

import Mathlib

/-!
# Trace-norm bounds for cosine Gram matrices (`CosTraceNorm` family)

For a family of angles `θ : Fin n → ℝ` we consider the *cosine matrix*

`cosMatrix θ i j = Real.cos (θ i - θ j)`.

It is the Gram matrix of the unit vectors `(cos (θ i), sin (θ i)) ∈ ℝ²`, hence real symmetric
and positive semidefinite, with all diagonal entries equal to `1`.

The main result `Brockian.CosTraceNorm3001` computes its Schatten `1`-norm (trace norm,
the sum of the absolute values of its eigenvalues): it is exactly `n`.  Because the matrix has
rank at most `2`, its Schatten `2`-norm (Frobenius norm) is at least `n / √2`, which is recorded
as a bound on `∑ i, ∑ j, cos (θ i - θ j) ^ 2`.
-/

open scoped BigOperators
open Matrix

namespace Brockian

variable {n : ℕ}

/-- The cosine matrix of a family of angles: `cosMatrix θ i j = cos (θ i - θ j)`. -/

theorem cosFrobeniusSq_ge (θ : Fin n → ℝ) :
    (n : ℝ) ^ 2 / 2 ≤ ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2 := by
  have key : 2 * ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2
      = (n : ℝ) ^ 2 + ∑ i, ∑ j, Real.cos (2 * θ i - 2 * θ j) := by
    have expand : ∀ i j : Fin n, 2 * Real.cos (θ i - θ j) ^ 2
        = 1 + Real.cos (2 * θ i - 2 * θ j) := by
      intro i j
      have h : 2 * θ i - 2 * θ j = 2 * (θ i - θ j) := by ring
      rw [h, Real.cos_sq]
      ring
    have hin : ∀ i : Fin n, 2 * ∑ j, Real.cos (θ i - θ j) ^ 2
        = (n : ℝ) + ∑ j, Real.cos (2 * θ i - 2 * θ j) := by
      intro i
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => expand i j), Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [Finset.mul_sum, Finset.sum_congr rfl (fun i _ => hin i), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sq]
  have hpos := cosSum_nonneg (fun k => 2 * θ k)
  simp only at hpos
  linarith

/-- **Frobenius (Schatten `2`) upper bound.**  All entries of the cosine matrix are bounded
by `1` in absolute value, so the sum of their squares is at most `n ^ 2`. -/
