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

lemma pow_one_add_expand_int (D : ℤ) (i : ℕ) :
    ∃ M : ℤ, (1 + D) ^ i = 1 + i * D + M * (D * D) := by
  induction i with
  | zero => exact ⟨0, by simp⟩
  | succ i ih =>
      obtain ⟨M, hM⟩ := ih
      refine ⟨i + M + M * D, ?_⟩
      rw [pow_succ, hM]
      push_cast
      ring

/-- Geometric sum modulo `D ^ 2` over `ℤ`. -/
