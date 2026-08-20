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

lemma pow_mod_eq {n : ℕ} {v : ℂ} (hv : v ^ n = 1) (x : ℕ) : v ^ (x % n) = v ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x n, pow_add, pow_mul, hv, one_pow, one_mul]

/-- If `v ^ n = 1` then `a ↦ v ^ a.val` is an additive-to-multiplicative character of `ZMod n`. -/
