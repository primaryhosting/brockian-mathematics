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

theorem cycleLaplacian_mulVec_fourierVec (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    cycleLaplacian n *ᵥ (fun j : Fin n => Complex.exp (2 * Real.pi * Complex.I * k * j / n))
      = ((2 - 2 * Real.cos (2 * Real.pi * k / n) : ℝ) : ℂ) •
        (fun j : Fin n => Complex.exp (2 * Real.pi * Complex.I * k * j / n)) := by
  have hn0 : n ≠ 0 := by omega
  have hv : ∀ j : Fin n,
      Complex.exp (2 * Real.pi * Complex.I * k * j / n) = fourierMat n j k := by
    intro j
    rw [fourierMat_apply_exp hn0]
    ring_nf
  funext i
  have h := congrFun (congrFun (laplacian_mul_fourier hn) i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal, cycleEig_eq hn0] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hv]
  rw [h, mul_comm]

/-- **Spectrum of the cycle Laplacian.**  For `n ≥ 3` the eigenvalues of the Laplacian of the
cycle graph `C n` are exactly the numbers `2 - 2 cos (2 π k / n)` for `k = 0, …, n - 1`. -/
