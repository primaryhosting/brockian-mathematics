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

theorem laplacian_mul_dft {n : ℕ} (hn : 3 ≤ n) :
    cycleLaplacian n * dftMatrix n = dftMatrix n * Matrix.diagonal (cycleEig n) := by
  have hn0 : n ≠ 0 := by omega
  haveI : NeZero n := ⟨hn0⟩
  ext i k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hrhs : ∑ j : Fin n, dftMatrix n i j * Matrix.diagonal (cycleEig n) j k
      = dftMatrix n i k * cycleEig n k := by
    simp [Matrix.diagonal_apply, eq_comm]
  rw [hrhs]
  have hlhs : ∀ j : Fin n, cycleLaplacian n i j * dftMatrix n j k
      = cycleVec n (i - j) * zetaN n ^ ((j : ℕ) * (k : ℕ)) := by
    intro j
    simp [cycleLaplacian, Matrix.circulant_apply, dftMatrix]
  rw [Finset.sum_congr rfl (fun j _ => hlhs j)]
  have hre : ∑ j : Fin n, cycleVec n (i - j) * zetaN n ^ ((j : ℕ) * (k : ℕ))
      = ∑ m : Fin n, cycleVec n m * zetaN n ^ (((i - m : Fin n) : ℕ) * (k : ℕ)) := by
    refine (Equiv.sum_comp (Equiv.subLeft i)
      (fun j : Fin n => cycleVec n (i - j) * zetaN n ^ ((j : ℕ) * (k : ℕ)))).symm.trans ?_
    refine Finset.sum_congr rfl ?_
    intro m _
    simp only [Equiv.subLeft_apply]
    rw [sub_sub_cancel]
  rw [hre]
  have hstep : ∀ m : Fin n, cycleVec n m * zetaN n ^ (((i - m : Fin n) : ℕ) * (k : ℕ))
      = zetaN n ^ ((i : ℕ) * (k : ℕ)) * (cycleVec n m * zetaN n ^ ((n - (m : ℕ)) * (k : ℕ))) := by
    intro m
    have hval : ((i - m : Fin n) : ℕ) = (n - (m : ℕ) + (i : ℕ)) % n := Fin.val_sub i m
    have hcong : (((i - m : Fin n) : ℕ) * (k : ℕ)) % n
        = ((n - (m : ℕ) + (i : ℕ)) * (k : ℕ)) % n := by
      rw [hval, Nat.mul_mod, Nat.mod_mod_of_dvd, ← Nat.mul_mod]
      exact dvd_rfl
    rw [zetaN_pow_congr hn0 hcong, add_mul, pow_add]
    ring
  rw [Finset.sum_congr rfl (fun m _ => hstep m), ← Finset.mul_sum, cycleVec_sum hn]
  simp [dftMatrix]

/-- The entries of the DFT matrix are the discrete Fourier characters. -/
