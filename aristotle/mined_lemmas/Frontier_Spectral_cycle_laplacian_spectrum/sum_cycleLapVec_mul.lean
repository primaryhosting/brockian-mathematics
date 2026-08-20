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

lemma sum_cycleLapVec_mul (hn : 3 ≤ n) (f : ZMod n → ℂ) :
    ∑ d : ZMod n, cycleLapVec n d * f d = 2 * f 0 - f 1 - f (-1) := by
  simp only [cycleLapVec_eq hn, sub_mul, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp

/-- Orthogonality of the additive characters of `ZMod n`. -/
