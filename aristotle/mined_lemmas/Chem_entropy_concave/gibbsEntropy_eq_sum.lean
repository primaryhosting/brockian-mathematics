import Mathlib

/-!
# Entropy Concave
Category: Chemistry
Target: Chem.entropy_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Chem

/-- The set of probability vectors indexed by `ι`: nonnegative entries summing to `1`. -/

theorem gibbsEntropy_eq_sum {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    gibbsEntropy p = ∑ i, Real.negMulLog (p i) := by
  simp [gibbsEntropy, Real.negMulLog, Finset.sum_neg_distrib]

/-- **The Gibbs entropy `-∑ pᵢ log pᵢ` is concave in the probability vector.** -/
