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

open Matrix Polynomial

variable {n : ℕ} [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `shift n i j = 1` iff `i - j = 1`. -/

lemma shift_pow_card : shift n ^ n = 1 := by
  rw [shift_pow]
  simp

-- If `ζ ^ n = 1` then powers of `ζ` only depend on the exponent mod `n`.
omit [NeZero n] in
