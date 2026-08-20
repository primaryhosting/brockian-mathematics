import Mathlib

/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- The full Catalan–Mihăilescu theorem, as a statement (it is *not* proved in this file):
the only pair of consecutive perfect powers is `8 = 2 ^ 3` and `9 = 3 ^ 2`. -/

lemma geom_sum_expand (d m : ℕ) :
    ∃ K, 2 * (∑ i ∈ Finset.range m, (1 + d) ^ i) = 2 * m + m * (m - 1) * d + K * (d * d) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨M, hM⟩ := pow_one_add_expand d m
      refine ⟨K + 2 * M, ?_⟩
      rw [Finset.sum_range_succ, Nat.mul_add, hK, hM]
      cases m with
      | zero => simp; ring
      | succ m => simp; ring

/-- Binomial expansion modulo `D ^ 2` over `ℤ`. -/
