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

lemma fourier_mul_inv : fourierMat n * fourierMatInv n = 1 := by
  ext i j
  simp only [Matrix.mul_apply, fourierMat, fourierMatInv, Matrix.of_apply]
  have key : ∀ k : ZMod n, ZMod.stdAddChar (i * k) * ((n : ℂ)⁻¹ * ZMod.stdAddChar (-(k * j)))
      = (n : ℂ)⁻¹ * ZMod.stdAddChar ((i - j) * k) := by
    intro k
    rw [show (i - j) * k = i * k + -(k * j) by ring, AddChar.map_add_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun k _ => key k), ← Finset.mul_sum, sum_stdAddChar_mul]
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  by_cases h : i = j
  · simp [h, Matrix.one_apply, hn]
  · simp [h, sub_eq_zero]

