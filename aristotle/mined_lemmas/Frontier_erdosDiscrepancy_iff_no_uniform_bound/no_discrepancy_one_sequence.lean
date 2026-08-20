import Mathlib

/-!
# Erdos Discrepancy
Category: Frontier — Prime Numbers
Target: Frontier.erdos_discrepancy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-- A `±1` sequence, indexed by the positive integers. -/

theorem no_discrepancy_one_sequence (f : ℕ → ℤ) (hf : IsPlusMinusOne f)
    (H : ∀ d n : ℕ, 0 < d → 0 < n → d * n ≤ 12 → |apSum f d n| ≤ 1) : False := by
  simp only [apSum] at H
  have h1 := H 1 4 (by norm_num) (by norm_num) (by norm_num)
  have h2 := H 1 6 (by norm_num) (by norm_num) (by norm_num)
  have h3 := H 1 10 (by norm_num) (by norm_num) (by norm_num)
  have h4 := H 1 8 (by norm_num) (by norm_num) (by norm_num)
  have h5 := H 3 2 (by norm_num) (by norm_num) (by norm_num)
  have h6 := H 3 4 (by norm_num) (by norm_num) (by norm_num)
  have h7 := H 5 2 (by norm_num) (by norm_num) (by norm_num)
  have h8 := H 6 2 (by norm_num) (by norm_num) (by norm_num)
  rw [show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) from rfl] at h5 h7 h8
  rw [show Finset.Icc 1 4 = ({1, 2, 3, 4} : Finset ℕ) from rfl] at h1 h6
  rw [show Finset.Icc 1 6 = ({1, 2, 3, 4, 5, 6} : Finset ℕ) from rfl] at h2
  rw [show Finset.Icc 1 8 = ({1, 2, 3, 4, 5, 6, 7, 8} : Finset ℕ) from rfl] at h4
  rw [show Finset.Icc 1 10 = ({1, 2, 3, 4, 5, 6, 7, 8, 9, 10} : Finset ℕ) from rfl] at h3
  simp only [abs_le] at h1 h2 h3 h4 h5 h6 h7 h8
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8
  have a1 := hf 1 (by norm_num)
  have a2 := hf 2 (by norm_num)
  have a3 := hf 3 (by norm_num)
  have a4 := hf 4 (by norm_num)
  have a5 := hf 5 (by norm_num)
  have a6 := hf 6 (by norm_num)
  have a7 := hf 7 (by norm_num)
  have a8 := hf 8 (by norm_num)
  have a9 := hf 9 (by norm_num)
  have a10 := hf 10 (by norm_num)
  have a12 := hf 12 (by norm_num)
  omega

/-- A quantitative form of the base case: the progression witnessing discrepancy `≥ 2`
can be found among those with `d * n ≤ 12`, i.e. using only the values `f 1, …, f 12`. -/
