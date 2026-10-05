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

theorem fourier_mul_fourierInv : fourier n * fourierInv n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  ext j m
  rw [Matrix.mul_apply]
  have hterm : ∀ k : ZMod n,
      fourier n j k * fourierInv n k m
        = (n : ℂ)⁻¹ * (zeta n ^ (j.val + (n - m.val))) ^ k.val := by
    intro k
    have h : zeta n ^ (j.val * k.val) * zeta n ^ (k.val * (n - m.val))
        = (zeta n ^ (j.val + (n - m.val))) ^ k.val := by
      rw [← pow_add, ← pow_mul]; congr 1; ring
    simp only [fourier, fourierInv]
    rw [mul_left_comm, h]
  rw [Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.mul_sum]
  rw [sum_zmod_eq_sum_range n (fun i => (zeta n ^ (j.val + (n - m.val))) ^ i)]
  by_cases hjm : j = m
  · subst hjm
    have hv : j.val + (n - j.val) = n := by have := ZMod.val_lt j; omega
    rw [hv, zeta_pow_n]
    simp [hn0]
  · have hjv : j.val ≠ m.val := fun h => hjm (by
      have := congrArg (Nat.cast : ℕ → ZMod n) h
      simpa [ZMod.natCast_val, ZMod.natCast_rightInverse] using this)
    have hjlt := ZMod.val_lt j
    have hmlt := ZMod.val_lt m
    have hne : zeta n ^ (j.val + (n - m.val)) ≠ 1 := by
      intro hcon
      have hdvd : n ∣ (j.val + (n - m.val)) :=
        (isPrimitiveRoot_zeta n).pow_eq_one_iff_dvd _ |>.mp hcon
      obtain ⟨c, hc⟩ := hdvd
      have hc0 : c ≠ 0 := by rintro rfl; omega
      have hc1 : c ≠ 1 := by rintro rfl; omega
      have h2c : n * 2 ≤ n * c := Nat.mul_le_mul_left n (by omega)
      omega
    have hpow : (zeta n ^ (j.val + (n - m.val))) ^ n = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, zeta_pow_n, one_pow]
    rw [geom_sum_eq hne, hpow]
    simp [hjm]

