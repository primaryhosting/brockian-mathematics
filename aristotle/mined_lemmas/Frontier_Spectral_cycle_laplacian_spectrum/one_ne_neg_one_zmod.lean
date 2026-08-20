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

open Complex Matrix ZMod AddChar Finset

/-- The generating vector of the cycle Laplacian: `2` at `0`, `-1` at `±1`, `0` elsewhere. -/

lemma one_ne_neg_one_zmod (hn : 3 ≤ n) : (1 : ZMod n) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by push_cast; linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

omit [NeZero n] in
/-- Rewriting of the generating vector as a combination of indicator functions. -/
