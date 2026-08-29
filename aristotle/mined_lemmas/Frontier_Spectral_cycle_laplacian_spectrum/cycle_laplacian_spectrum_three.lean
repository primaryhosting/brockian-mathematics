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

theorem cycle_laplacian_spectrum_three : spectrum ℂ (cycleLaplacian 3) = {0, 3} := by
  rw [cycle_laplacian_spectrum 3 le_rfl]
  have h0 : (2 * Real.pi * 0 / 3 : ℝ) = 0 := by ring
  have h1 : (2 * Real.pi * 1 / 3 : ℝ) = Real.pi - Real.pi / 3 := by ring
  have h2 : (2 * Real.pi * 2 / 3 : ℝ) = Real.pi + Real.pi / 3 := by ring
  have e1 : Real.cos (2 * Real.pi * 1 / 3) = -(1 / 2) := by
    rw [h1, Real.cos_pi_sub, Real.cos_pi_div_three]
  have e2 : Real.cos (2 * Real.pi * 2 / 3) = -(1 / 2) := by
    rw [h2, Real.cos_add, Real.cos_pi_div_three]
    simp
  have hr : (Finset.range 3 : Set ℕ) = {0, 1, 2} := by
    ext x; simp; omega
  rw [hr]
  simp only [Set.image_insert_eq, Set.image_singleton, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, h0, e1, e2, Real.cos_zero]
  norm_num

end Frontier.Spectral

