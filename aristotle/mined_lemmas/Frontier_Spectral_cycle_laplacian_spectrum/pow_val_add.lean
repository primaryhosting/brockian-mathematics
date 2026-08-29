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

open Complex Matrix

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with
diagonal `2` and `-1` on the two cyclic off-diagonals (indices are taken in `ZMod n`). -/

lemma pow_val_add {ζ : ℂ} (hζ : ζ ^ n = 1) (a b : ZMod n) :
    ζ ^ (a + b).val = ζ ^ a.val * ζ ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) n]
  rw [pow_add, pow_mul, hζ, one_pow, one_mul]

