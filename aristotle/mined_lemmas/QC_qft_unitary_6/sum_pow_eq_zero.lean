/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open scoped Real

namespace QC

open Complex Matrix Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma sum_pow_eq_zero {x : ℂ} {n : ℕ} (hxn : x ^ n = 1) (hx : x ≠ 1) :
    ∑ j : Fin n, x ^ (j : ℕ) = 0 := by
  have h : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := geom_sum_mul x n
  rw [hxn, sub_self] at h
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have : ∑ i ∈ Finset.range n, x ^ i = 0 := by
    rcases mul_eq_zero.mp h with h' | h'
    · exact h'
    · exact absurd h' hx1
  rw [Fin.sum_univ_eq_sum_range (fun i => x ^ i) n]
  exact this

/-- Orthogonality of the rows of the QFT matrix. -/
