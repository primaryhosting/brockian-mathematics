/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier.Spectral

open Matrix Finset

/-- The graph Laplacian of the cycle graph `C n`, as the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma succ_val_iff (a b : ZMod n) : (a.val + 1) % n = b.val ↔ a + 1 = b := by
  constructor
  · intro h
    have : ((a.val + 1 : ℕ) : ZMod n) = ((b.val : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff', h, Nat.mod_eq_of_lt b.val_lt]
    simpa [ZMod.natCast_val, ZMod.natCast_zmod_val] using this
  · intro h
    have : ((a.val + 1 : ℕ) : ZMod n) = ((b.val : ℕ) : ZMod n) := by
      push_cast
      simpa [ZMod.natCast_val, ZMod.natCast_zmod_val] using h
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rwa [Nat.mod_eq_of_lt b.val_lt] at this

omit [NeZero n] in
