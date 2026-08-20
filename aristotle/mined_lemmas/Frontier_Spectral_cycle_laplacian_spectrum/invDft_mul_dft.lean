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

lemma invDft_mul_dft : invDftMatrix n * dftMatrix n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  ext j l
  rw [Matrix.mul_apply]
  have key : ∀ k : ZMod n, invDftMatrix n j k * dftMatrix n k l
      = (n : ℂ)⁻¹ * ZMod.stdAddChar ((l - j) * k) := by
    intro k
    simp only [dftMatrix, invDftMatrix, Matrix.of_apply]
    rw [show (l - j) * k = (-(j * k)) + k * l by ring, AddChar.map_add_eq_mul]
    ring
  simp only [key, ← Finset.mul_sum, stdAddChar_sum]
  by_cases h : j = l
  · subst h; simp [inv_mul_cancel₀ hn0]
  · simp [h, sub_eq_zero, Ne.symm h]

