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
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Polynomial Matrix Complex

variable (n : ℕ) [NeZero n]

/-- The cyclic shift matrix on `ZMod n`: `(S *ᵥ v) i = v (i + 1)`. -/

lemma pow_eq_pow_of_natCast_eq {z : ℂ} (hz : z ^ n = 1) {a b : ℕ}
    (hab : (a : ZMod n) = (b : ZMod n)) : z ^ a = z ^ b := by
  have h : a % n = b % n := (ZMod.natCast_eq_natCast_iff' a b n).mp hab
  rw [← pow_mod_eq n hz a, ← pow_mod_eq n hz b, h]

