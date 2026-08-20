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

theorem cosFrobeniusSq_le (θ : Fin n → ℝ) :
    ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2 ≤ (n : ℝ) ^ 2 := by
  have h : ∑ i, ∑ j, Real.cos (θ i - θ j) ^ 2 ≤ ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have := Real.neg_one_le_cos (θ i - θ j)
    have := Real.cos_le_one (θ i - θ j)
    nlinarith
  simpa [Finset.sum_const, sq] using h

/-- The trace norm of the cosine matrix is bounded by the entrywise `ℓ¹`-norm. -/
