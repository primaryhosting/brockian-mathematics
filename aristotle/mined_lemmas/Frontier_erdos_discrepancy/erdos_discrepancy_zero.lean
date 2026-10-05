/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- A `±1`-sequence: a function `f : ℕ → ℤ` taking only the values `1` and `-1`
on the positive integers. -/

theorem erdos_discrepancy_zero (f : ℕ → ℤ) (hf : PlusMinusOne f) :
    HasDiscrepancyExceeding f 0 := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  have h := hf 1 le_rfl
  simp only [apSum, Finset.Icc_self, Finset.sum_singleton, one_mul]
  rcases h with h | h <;> rw [h] <;> norm_num

/-- **Erdős discrepancy problem, base case `C = 1`.**
Every `±1`-sequence `f : ℕ → ℤ` admits a homogeneous arithmetic progression
`d, 2d, …, nd` (with `d, n ≥ 1`) along which the partial sum
`f d + f (2d) + ⋯ + f (nd)` has absolute value greater than `1`.

Equivalently: no `±1`-sequence has discrepancy at most `1` on homogeneous
arithmetic progressions.  Only the first `12` terms of the sequence are needed,
which is optimal (there are `±1` sequences of length `11` with discrepancy `1`). -/
