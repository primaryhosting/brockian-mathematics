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

/-
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Brockian.GoldbachComb

/-- The set of Goldbach parts of `n`: primes `p ≤ n` such that `n - p` is also prime.
Thus `p ∈ goldbachParts n` exactly when `p + (n - p) = n` is a Goldbach decomposition. -/

noncomputable def cov (s : Finset ℕ) (f g : ℕ → ℝ) : ℝ :=
  (∑ p ∈ s, f p * g p) / s.card - ((∑ p ∈ s, f p) / s.card) * ((∑ p ∈ s, g p) / s.card)

/-- **Goldbach Covariance Transfer.**  For every `n` and all real weights `f, g`, the
empirical covariance of `f` and `g` over the Goldbach parts of `n` is unchanged when both
weights are transported along the Goldbach reflection `p ↦ n - p` (which exchanges the two
summands of each Goldbach decomposition of `n`). -/
