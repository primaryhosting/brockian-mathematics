import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

lemma adj_mul_dft : adjC12 * dft12 = dft12 * Matrix.diagonal (fun k => ((muC12 k : ℝ) : ℂ)) := by
  ext i l
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ j : ZMod 12, adjC12 i j * dft12 j l
      = zeta12 ((i + 1) * l) + zeta12 ((i - 1) * l) := by
    simp only [adj_apply_split, dft12, add_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i+1) (fun j => zeta12 (j * l)),
      Finset.sum_ite_eq' Finset.univ (i-1) (fun j => zeta12 (j * l))]
    simp
  have hR : ∑ j : ZMod 12, dft12 i j * Matrix.diagonal (fun k => ((muC12 k : ℝ) : ℂ)) j l
      = zeta12 (i * l) * ((muC12 l : ℝ) : ℂ) := by
    simp [Matrix.diagonal, dft12]
  have e1 : zeta12 ((i + 1) * l) = zeta12 (i * l) * zeta12 l := by
    rw [show (i + 1) * l = i * l + l by ring, zeta12_add]
  have e2 : zeta12 ((i - 1) * l) = zeta12 (i * l) * zeta12 (-l) := by
    rw [show (i - 1) * l = i * l + -l by ring, zeta12_add]
  rw [hL, hR, ← zeta12_add_neg l, e1, e2]
  ring

/-- **Hückel theory for the cycle `C₁₂`.**  The characteristic polynomial of the adjacency
matrix of the cycle graph `C₁₂` factors as `∏_{k=0}^{11} (X - 2 cos(2πk/12))`; i.e. the
adjacency eigenvalues of `C₁₂` are exactly `2 cos(2πk/12)` for `k = 0, …, 11`. -/
