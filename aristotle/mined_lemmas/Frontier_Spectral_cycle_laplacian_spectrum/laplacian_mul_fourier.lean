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

theorem laplacian_mul_fourier (hn : 3 ≤ n) :
    cycleLaplacian n * fourier n =
      fourier n * Matrix.diagonal (fun k : ZMod n => ((cycleEigenvalue n k.val : ℝ) : ℂ)) := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  have hrow : ∀ m : ZMod n, cycleLaplacian n j m * fourier n m k
      = (if m = j then 2 * fourier n m k else 0) - (if m = j + 1 then fourier n m k else 0)
        - (if m = j - 1 then fourier n m k else 0) := by
    intro m
    rw [cycleLaplacian_apply_eq n hn]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun m _ => hrow m)]
  simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hplus : fourier n (j + 1) k = fourier n j k * zeta n ^ k.val := fourier_shift n hn j k
  have hminus : fourier n (j - 1) k = fourier n j k * (zeta n ^ k.val)⁻¹ := by
    have h := fourier_shift n hn (j - 1) k
    rw [sub_add_cancel] at h
    have hz : zeta n ^ k.val ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
    show zeta n ^ ((j - 1).val * k.val) = zeta n ^ (j.val * k.val) * (zeta n ^ k.val)⁻¹
    rw [h, mul_assoc, mul_inv_cancel₀ hz, mul_one]
  rw [hplus, hminus, ← zeta_eigen n k.val]
  ring

end

/-- **The Laplacian spectrum of the cycle graph `C n`.**  For `n ≥ 3`, the eigenvalues of the graph
Laplacian of the cycle `C n` (the circulant matrix with `2` on the diagonal and `-1` on the two
cyclic off-diagonals) are exactly the numbers `2 - 2 * cos (2 * π * k / n)` for `k ∈ range n`. -/
