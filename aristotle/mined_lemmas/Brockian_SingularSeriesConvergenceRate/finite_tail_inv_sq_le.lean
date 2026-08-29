/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

open Finset

/-- Auxiliary tail estimate: for `1 ≤ Q` and any `n`, the finite sum
`∑_{k < n} C / (k + Q)^2` is at most `2 * C / Q`. -/

lemma finite_tail_inv_sq_le {C : ℝ} (hC : 0 ≤ C) {Q : ℕ} (hQ : 1 ≤ Q) (n : ℕ) :
    ∑ k ∈ range n, C / ((k + Q : ℕ) : ℝ) ^ 2 ≤ 2 * C / Q := by
  have hreindex :
      ∑ k ∈ range n, C / ((k + Q : ℕ) : ℝ) ^ 2
        = ∑ i ∈ Ico Q (n + Q), C / (i : ℝ) ^ 2 := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp [add_comm]
  have hset : Ico Q (n + Q) = Ioo (Q - 1) (n + Q) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_Ioo]
    omega
  have hkey : ∑ i ∈ Ioo (Q - 1) (n + Q), ((i : ℝ) ^ 2)⁻¹ ≤ 2 / (((Q - 1 : ℕ) : ℝ) + 1) :=
    sum_Ioo_inv_sq_le _ _
  have hcast : ((Q - 1 : ℕ) : ℝ) + 1 = (Q : ℝ) := by
    have : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
      have : (1 : ℕ) ≤ Q := hQ
      push_cast [Nat.cast_sub this]
      ring
    rw [this]; ring
  rw [hcast] at hkey
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hQ
  calc ∑ k ∈ range n, C / ((k + Q : ℕ) : ℝ) ^ 2
      = C * ∑ i ∈ Ioo (Q - 1) (n + Q), ((i : ℝ) ^ 2)⁻¹ := by
        rw [hreindex, hset, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [div_eq_mul_inv]
    _ ≤ C * (2 / (Q : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hkey hC
    _ = 2 * C / Q := by ring

/-- **Effective convergence rate for a singular series.**

If the terms `a q` of a singular-series-type expansion satisfy the standard
majorization `|a q| ≤ C / q²` for all `q ≥ 1`, then the series converges and the
truncation at level `Q ≥ 1` incurs an error of at most `2 * C / Q`; that is, the
truncated singular series `∑_{q < Q} a q` approximates the full singular series
`∑' q, a q` with an explicit `O(1/Q)` rate. -/
