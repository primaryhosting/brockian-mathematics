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

lemma geom_sum_expand_int (D : ℤ) (m : ℕ) :
    ∃ K : ℤ, 2 * (∑ i ∈ Finset.range m, (1 + D) ^ i)
      = 2 * m + m * ((m : ℤ) - 1) * D + K * (D * D) := by
  induction m with
  | zero => exact ⟨0, by simp⟩
  | succ m ih =>
      obtain ⟨K, hK⟩ := ih
      obtain ⟨M, hM⟩ := pow_one_add_expand_int D m
      refine ⟨K + 2 * M, ?_⟩
      rw [Finset.sum_range_succ, mul_add, hK, hM]
      push_cast
      ring

/-- For odd `q`, `Y + 1` divides `Y ^ q + 1` with the alternating geometric sum as cofactor. -/
