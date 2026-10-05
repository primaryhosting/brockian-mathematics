import Mathlib

/-!
# Cos Trace Norm 1597
Category: Brockian Corpus
Target: Brockian.CosTraceNorm1597
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Matrix

namespace Brockian

/-- The cosine Gram matrix of a family of angles `x : Fin n → ℝ`:
its `(i, j)` entry is `cos (x i - x j)`. -/

theorem cosMatrix_eigenvalue_le {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ (cosMatrix_isHermitian x).eigenvalues i ∧
      (cosMatrix_isHermitian x).eigenvalues i ≤ n := by
  have hpos : ∀ j, 0 ≤ (cosMatrix_isHermitian x).eigenvalues j := fun j =>
    (cosMatrix_posSemidef x).eigenvalues_nonneg j
  refine ⟨hpos i, ?_⟩
  have hsum : ∑ j, (cosMatrix_isHermitian x).eigenvalues j = n := by
    have h1 : traceNorm (cosMatrix_isHermitian x)
        = ∑ j, (cosMatrix_isHermitian x).eigenvalues j :=
      Finset.sum_congr rfl fun j _ => abs_of_nonneg (hpos j)
    rw [← h1]; exact CosTraceNorm1597 x
  calc (cosMatrix_isHermitian x).eigenvalues i
      ≤ ∑ j, (cosMatrix_isHermitian x).eigenvalues j :=
        Finset.single_le_sum (fun j _ => hpos j) (Finset.mem_univ i)
    _ = n := hsum

end Brockian

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

