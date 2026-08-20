import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Frontier.Spectral

open Complex Matrix Polynomial

/-- The cyclic shift matrix indexed by `ZMod n`: the circulant matrix whose `(i, j)` entry is `1`
exactly when `i - j = 1`. -/

lemma cycleShift_pow_card (n : ℕ) [NeZero n] : (cycleShift n) ^ n = 1 := by
  rw [cycleShift_pow]
  simp

/-- For `n ≥ 3` the three residues `0`, `1`, `-1` are pairwise distinct in `ZMod n`. -/
