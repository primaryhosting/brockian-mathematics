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

lemma two_ne_zero_zmod (hn : 3 ≤ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
  have hd := (ZMod.natCast_eq_zero_iff 2 n).mp this
  have := Nat.le_of_dvd (by norm_num) hd
  omega

