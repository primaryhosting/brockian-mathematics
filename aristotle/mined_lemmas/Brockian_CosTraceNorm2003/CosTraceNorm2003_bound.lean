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

import Mathlib

/-!
# Cos Trace Norm 2003
Category: Brockian Corpus
Target: Brockian.CosTraceNorm2003
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Brockian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace norm (Schatten 1-norm) of a Hermitian real matrix, defined as the sum of the
absolute values of its eigenvalues (and `0` on non-Hermitian matrices). -/

theorem CosTraceNorm2003_bound (w θ : n → ℝ) (M : ℝ) (hM : ∀ i, |w i| ≤ M) :
    traceNorm (cosGram w θ) ≤ (Fintype.card n : ℝ) * M ^ 2 := by
  rw [CosTraceNorm2003]
  calc ∑ i, (w i) ^ 2 ≤ ∑ _i : n, M ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM i) 2
    _ = (Fintype.card n : ℝ) * M ^ 2 := by
        simp [Finset.card_univ]

end Brockian

