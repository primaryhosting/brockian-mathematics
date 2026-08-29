/-
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier — Spectral Geometry
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(The header above is repeated as a plain comment at the very top of the file, since Lean does not
allow a module docstring to precede the `import` commands.)

We model the cycle graph `C n` on the vertex set `ZMod n` and its graph Laplacian as the circulant
matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals.  Conjugating by the
discrete Fourier matrix `F j k = exp (2 π i j k / n)` diagonalises it, which identifies the spectrum
as `{2 - 2 cos (2 π k / n) : k ∈ range n}`.
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

/-- The graph Laplacian of the cycle graph `C n`, indexed by `ZMod n`:
the circulant matrix with `2` on the diagonal and `-1` on the two cyclic off-diagonals. -/

theorem zeta_eigen (k : ℕ) :
    2 - zeta n ^ k - (zeta n ^ k)⁻¹ = ((cycleEigenvalue n k : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [cycleEigenvalue, zeta]
  set t : ℝ := 2 * Real.pi * k / n with ht
  have h1 : (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    field_simp
  rw [h1, ← Complex.exp_neg]
  have h2 : -((t : ℂ) * Complex.I) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h2, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The discrete Fourier matrix `F j k = ζ ^ (j * k) = exp (2 π i j k / n)`. -/
