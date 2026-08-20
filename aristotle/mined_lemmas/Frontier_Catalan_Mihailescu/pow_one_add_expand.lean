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

lemma pow_one_add_expand (d i : ℕ) : ∃ M, (1 + d) ^ i = 1 + i * d + M * (d * d) := by
  induction i with
  | zero => exact ⟨0, by ring⟩
  | succ i ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨i + M + M * d, ?_⟩
      rw [pow_succ, hM]
      ring

/-- Geometric sum modulo `d ^ 2`: `2 * ∑ i < m, (1 + d) ^ i = 2 * m + m * (m - 1) * d + K * d ^ 2`. -/
