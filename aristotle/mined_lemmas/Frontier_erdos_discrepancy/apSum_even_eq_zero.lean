/-
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
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

namespace Frontier

/-- A `±1` sequence, indexed by the positive naturals (the value at `0` is irrelevant). -/

theorem apSum_even_eq_zero (hf : IsPlusMinusOne f) (hb : HasDiscrepancyAtMost f 1)
    {d : ℕ} (hd : 1 ≤ d) (j : ℕ) : apSum f d (2 * j) = 0 := by
  obtain ⟨c, hc⟩ := two_dvd_apSum_sub hf hd (2 * j)
  have hle : |apSum f d (2 * j)| ≤ (1 : ℤ) := by simpa using hb d (2 * j) hd
  rw [abs_le] at hle
  push_cast at hc
  omega

/-- If the discrepancy is at most `1`, consecutive terms of a homogeneous AP pair off:
`f ((2j+1) d) + f ((2j+2) d) = 0`. -/
