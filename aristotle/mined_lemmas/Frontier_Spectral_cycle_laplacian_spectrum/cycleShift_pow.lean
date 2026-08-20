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

lemma cycleShift_pow (n : ℕ) [NeZero n] (k : ℕ) :
    (cycleShift n) ^ k = Matrix.circulant (Pi.single ((k : ZMod n)) 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, cycleShift, circulant_single_mul_single]; push_cast; ring_nf

/-- The shift matrix has order dividing `n`. -/
