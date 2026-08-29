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
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- The total "excess above `theta`" is at most the sum of the eigenvalues that exceed
`theta`: the indices below the threshold contribute a nonpositive amount, and subtracting
`n * theta` (with `theta ≥ 0`) only decreases the sum. -/

theorem sum_sq_filter_le {d : ℕ} (ev : Fin d → ℝ) (theta : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), (ev i) ^ 2
      ≤ ∑ i, (ev i) ^ 2 := by
  classical
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  positivity

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**
If the eigenvalues `ev : Fin d → ℝ` have total mass exceeding `theta * d` (for a threshold
`theta ≥ 0`), and `n` is the number of eigenvalues strictly above `theta`, then
`((∑ ev) - theta * d)^2 ≤ n * ∑ (ev i)^2`. -/
