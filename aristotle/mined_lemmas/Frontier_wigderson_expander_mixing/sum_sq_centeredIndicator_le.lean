/-
# Wigderson Expander Mixing
Category: Frontier Abel
Target: Frontier.wigderson_expander_mixing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

variable {n : ℕ}

/-- The *centered indicator* of a vertex set `S` inside a vertex set of size `n`:
the indicator function of `S` minus its mean value `|S|/n`.  It is orthogonal to
the all-ones vector. -/

lemma sum_sq_centeredIndicator_le (hn : 0 < n) (S : Finset (Fin n)) :
    ∑ i, centeredIndicator S i ^ 2 ≤ (S.card : ℝ) := by
  rw [sum_sq_centeredIndicator hn S]
  have : 0 ≤ (S.card : ℝ) ^ 2 / (n : ℝ) := by positivity
  linarith

/-- **Key intermediate lemma.**  For a `d`-regular weighted graph (all row and column
sums of `A` equal `d`), the bilinear form of `A` applied to the centered indicators of
`S` and `T` is exactly the edge discrepancy `e(S,T) - d|S||T|/n`. -/
