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

lemma pow_val_add {n : ℕ} [NeZero n] {v : ℂ} (hv : v ^ n = 1) (a b : ZMod n) :
    v ^ (a + b).val = v ^ a.val * v ^ b.val := by
  rw [ZMod.val_add, pow_mod_eq hv, pow_add]

/-- Every `n`-th root of unity is an eigenvalue of the shift matrix, with the discrete Fourier
eigenvector `j ↦ z⁻¹ ^ j`. -/
