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

open Matrix Finset

/-- The graph Laplacian of the cycle `C n`, as the `n × n` circulant matrix (indexed by
`ZMod n`) with diagonal entries `2` and `-1` on the two cyclic off-diagonals. -/

lemma fourierMatrixInv_mul : fourierMatrixInv n * fourierMatrix n = 1 := by
  ext i l
  rw [Matrix.mul_apply]
  simp only [fourierMatrix, fourierMatrixInv, Matrix.one_apply]
  have key : ∀ j : ZMod n, ((n : ℂ)⁻¹ * ZMod.stdAddChar (-(i * j))) * ZMod.stdAddChar (j * l)
      = (n : ℂ)⁻¹ * ZMod.stdAddChar ((l - i) * j) := by
    intro j
    rw [show ((l - i) * j) = -(i * j) + j * l by ring, AddChar.map_add_eq_mul]
    ring
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp only [key, ← Finset.mul_sum, sum_stdAddChar_mul, sub_eq_zero,
    eq_comm (a := l) (b := i)]
  split_ifs <;> simp [inv_mul_cancel₀ hn0]

/-- The Fourier matrix as a unit of the matrix algebra. -/
