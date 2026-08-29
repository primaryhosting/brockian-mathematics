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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` lines to precede every other command, including module
docstrings, so the requested header comment appears immediately after the import.)
-/

open scoped BigOperators

namespace Brockian.GoldbachComb

/-- The Goldbach representation count of `n`: the number of ordered pairs `(a, n - a)`
with `a ≤ n` such that both `a` and `n - a` are prime. -/

theorem GoldbachCovarianceTransfer (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (goldbachCount n : ℝ)
      = ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1),
          (if p + q ≤ N then primeIndicator p * primeIndicator q else 0) := by
  rw [← sum_convolution_eq_bilinear primeIndicator N]
  exact Finset.sum_congr rfl fun n _ => goldbachCount_eq_sum n

end Brockian.GoldbachComb

