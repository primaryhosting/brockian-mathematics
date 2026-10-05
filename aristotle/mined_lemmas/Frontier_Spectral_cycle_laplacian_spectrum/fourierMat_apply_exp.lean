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

open Matrix

/-- The graph Laplacian of the cycle graph `C n`: the `n × n` circulant matrix with `2` on the
diagonal and `-1` on the two cyclic off-diagonals. -/

lemma fourierMat_apply_exp {n : ℕ} (hn : n ≠ 0) (i j : Fin n) :
    fourierMat n i j = Complex.exp (2 * Real.pi * Complex.I * i * j / n) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [fourierMat, Matrix.of_apply, cycleRoot, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- The discrete Fourier vectors `v k (j) = exp (2 π I k j / n)` are eigenvectors of the cycle
Laplacian, with eigenvalue `2 - 2 cos (2 π k / n)`. -/
