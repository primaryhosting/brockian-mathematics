/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Finset

namespace Brockian

/-- The comparison series `q ↦ C / q ^ 2` used to control a singular series. -/

lemma sum_range_shift_inv_sq_le {C : ℝ} (hC : 0 ≤ C) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    ∑ i ∈ range n, C / ((i : ℝ) + N) ^ 2 ≤ 2 * C / N := by
  have hcast : ∀ i ∈ range n, C / ((i : ℝ) + N) ^ 2 = C * (((N + i : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro i _
    push_cast
    rw [div_eq_mul_inv, add_comm (N : ℝ) (i : ℝ)]
  rw [Finset.sum_congr rfl hcast, ← Finset.mul_sum]
  have hIco : ∑ i ∈ range n, (((N + i : ℕ) : ℝ) ^ 2)⁻¹
      = ∑ j ∈ Finset.Ico N (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp
  have hsub : Finset.Ico N (N + n) ⊆ Finset.Ioo (N - 1) (N + n) := by
    intro j hj
    simp only [Finset.mem_Ico] at hj
    simp only [Finset.mem_Ioo]
    exact ⟨by omega, hj.2⟩
  have hnn : ∀ j ∈ Finset.Ioo (N - 1) (N + n), j ∉ Finset.Ico N (N + n) →
      (0 : ℝ) ≤ (((j : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro j _ _
    positivity
  have h1 : ∑ j ∈ Finset.Ico N (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹
      ≤ ∑ j ∈ Finset.Ioo (N - 1) (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub hnn
  have h2 : ∑ j ∈ Finset.Ioo (N - 1) (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹
      ≤ 2 / (((N - 1 : ℕ) : ℝ) + 1) := sum_Ioo_inv_sq_le (N - 1) (N + n)
  have hcast2 : (((N - 1 : ℕ) : ℝ) + 1) = (N : ℝ) := by
    have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      have := Nat.cast_sub (R := ℝ) hN
      simpa using this
    rw [this]; ring
  rw [hcast2] at h2
  calc C * ∑ i ∈ range n, (((N + i : ℕ) : ℝ) ^ 2)⁻¹
      = C * ∑ j ∈ Finset.Ico N (N + n), (((j : ℕ) : ℝ) ^ 2)⁻¹ := by rw [hIco]
    _ ≤ C * (2 / (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (h1.trans h2) hC
    _ = 2 * C / N := by ring

/--
**Singular series convergence rate.**

If the terms `a q` of a series (e.g. the local densities making up a Hardy–Littlewood
singular series) satisfy the effective bound `|a q| ≤ C / q ^ 2` for all `q ≥ 1`, then the
series converges and its truncation at level `N` approximates the full sum with the
effective error bound `2 * C / N`.
-/
