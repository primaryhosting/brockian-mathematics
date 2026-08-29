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

theorem pair_eq_zero (hf : IsPlusMinusOne f) (hb : HasDiscrepancyAtMost f 1)
    {d : ℕ} (hd : 1 ≤ d) (j : ℕ) : f ((2 * j + 1) * d) + f ((2 * j + 2) * d) = 0 := by
  have h0 : apSum f d (2 * j) = 0 := apSum_even_eq_zero hf hb hd j
  have h1 : apSum f d (2 * (j + 1)) = 0 := apSum_even_eq_zero hf hb hd (j + 1)
  have e1 : apSum f d (2 * j + 1) = apSum f d (2 * j) + f ((2 * j + 1) * d) := apSum_succ f d (2 * j)
  have e2 : apSum f d (2 * j + 2) = apSum f d (2 * j + 1) + f ((2 * j + 2) * d) :=
    apSum_succ f d (2 * j + 1)
  have h1' : apSum f d (2 * j + 2) = 0 := by rw [show 2 * j + 2 = 2 * (j + 1) by ring]; exact h1
  omega

/-- **Base case of the Erdős discrepancy problem.**  No `±1` sequence has discrepancy `≤ 1`
on homogeneous arithmetic progressions. -/
