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

lemma circulant_single_mulVec (a : ZMod n) (w : ZMod n → ℂ) :
    Matrix.circulant (Pi.single a (1 : ℂ)) *ᵥ w = fun i => w (i - a) := by
  funext i
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single (i - a)]
  · rw [Matrix.circulant_apply, sub_sub_cancel, Pi.single_eq_same, one_mul]
  · intro b _ hb
    have h : i - b ≠ a := fun h => hb (by rw [← h]; ring)
    simp [Matrix.circulant_apply, h]
  · simp

