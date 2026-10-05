import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
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

namespace Frontier.Spectral

open Matrix

/-- The graph Laplacian of the cycle graph `C n`: the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma pow_mod_of_pow_eq_one {n : ℕ} {z : ℂ} (hz : z ^ n = 1) (a : ℕ) :
    z ^ (a % n) = z ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a n, pow_add, pow_mul, hz, one_pow, one_mul]

/-- Orthogonality of characters: the powers of an `n`-th root of unity sum to `n` or to `0`. -/
