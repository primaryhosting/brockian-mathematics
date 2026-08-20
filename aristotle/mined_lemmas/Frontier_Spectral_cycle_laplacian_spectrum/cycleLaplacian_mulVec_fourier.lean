/-
# Cycle Laplacian Spectrum
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_laplacian_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cycle Laplacian Spectrum
Category: Frontier Spectral
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

open Complex Finset Matrix

/-! ## Definitions -/

/-- The `n`-th root of unity `exp (2πI/n)`. -/

theorem cycleLaplacian_mulVec_fourier {n : ℕ} (hn : 3 ≤ n) (k : Fin n) :
    (cycleLaplacian n).mulVec
        (fun j : Fin n => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℕ) * (j : ℕ) / (n : ℂ)))
      = ((2 - 2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ) •
        (fun j : Fin n =>
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℕ) * (j : ℕ) / (n : ℂ))) := by
  have hn0 : n ≠ 0 := by omega
  funext i
  have h := congrFun (congrFun (laplacian_mul_dft hn) i) k
  have hrhs : ∑ j : Fin n, dftMatrix n i j * Matrix.diagonal (cycleEig n) j k
      = dftMatrix n i k * cycleEig n k := by
    simp [Matrix.diagonal_apply, eq_comm]
  rw [Matrix.mul_apply, Matrix.mul_apply, hrhs] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
    ← dftMatrix_apply_eq_exp hn0]
  rw [h, cycleEig]
  ring

/-! ## The main theorem -/

/-- **Cycle Laplacian spectrum.** For `n ≥ 3`, the spectrum of the Laplacian of the cycle
graph `C n` (modelled as the circulant matrix with diagonal `2` and `-1` on the two cyclic
off-diagonals) is exactly `{2 - 2 cos (2πk/n) : k ∈ range n}`. -/
