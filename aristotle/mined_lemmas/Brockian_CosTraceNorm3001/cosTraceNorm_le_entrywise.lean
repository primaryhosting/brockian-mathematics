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

theorem cosTraceNorm_le_entrywise (θ : Fin n → ℝ) :
    traceNorm (cosMatrix_isHermitian θ) ≤ ∑ i, ∑ j, |Real.cos (θ i - θ j)| := by
  have hdiag : (n : ℝ) = ∑ i : Fin n, |Real.cos (θ i - θ i)| := by simp
  rw [CosTraceNorm3001 θ, hdiag]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Finset.single_le_sum (f := fun j => |Real.cos (θ i - θ j)|)
    (fun j _ => abs_nonneg _) (Finset.mem_univ i)

/-- **Trace norm versus Frobenius norm.**  The square of the trace norm of the cosine matrix is
at most twice the sum of the squares of its entries; this is sharp, reflecting that the matrix
has rank at most `2`. -/
