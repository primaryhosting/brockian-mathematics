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

lemma fourier_mul_inv {n : ℕ} (hn : n ≠ 0) : fourierMat n * fourierMatInv n = 1 := by
  have hw := cycleRoot_pow_n hn
  have hpow : ∀ m : ℕ, (cycleRoot n ^ m) ^ n = 1 := by
    intro m; rw [← pow_mul, mul_comm, pow_mul, hw, one_pow]
  have hne : ∀ m : ℕ, cycleRoot n ^ m ≠ 0 := fun m => pow_ne_zero _ (cycleRoot_ne_zero n)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  set z : ℂ := cycleRoot n ^ i.val * (cycleRoot n ^ j.val)⁻¹ with hzdef
  have hzn : z ^ n = 1 := by
    rw [hzdef, mul_pow, hpow, inv_pow, hpow, inv_one, mul_one]
  have hterm : ∀ p : Fin n, (fourierMat n i p) * (fourierMatInv n p j) = (n:ℂ)⁻¹ * z ^ (p : ℕ) := by
    intro p
    simp only [fourierMat, fourierMatInv, Matrix.of_apply, hzdef, mul_pow]
    rw [pow_mul, mul_comm p.val j.val, pow_mul, ← inv_pow]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hterm p), ← Finset.mul_sum, sum_pow_eq hzn]
  by_cases hij : i = j
  · have hz1 : z = 1 := by rw [hzdef, hij, mul_inv_cancel₀ (hne _)]
    rw [if_pos hz1, if_pos hij, inv_mul_cancel₀ hnC]
  · have hz1 : z ≠ 1 := by
      intro h
      rw [hzdef, mul_inv_eq_one₀ (hne _)] at h
      exact hij (Fin.ext ((cycleRoot_isPrimitiveRoot hn).pow_inj i.isLt j.isLt h))
    rw [if_neg hz1, if_neg hij, mul_zero]

/-- The columns of the discrete Fourier matrix diagonalise the cycle Laplacian. -/
