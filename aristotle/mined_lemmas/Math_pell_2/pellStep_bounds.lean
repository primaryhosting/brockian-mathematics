/-!
# Pell 2
Category: Pure Mathematics
Target: Math.pell_2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The Pell equation `x² − 2·y² = 1` has a nontrivial integer solution,
i.e. one with `y ≠ 0` (equivalently, a solution other than `(±1, 0)`).
Witness: `3² − 2·2² = 9 − 8 = 1`. -/

theorem pellStep_bounds (n : ℕ) :
    1 ≤ (pellStep n).1 ∧ 0 ≤ (pellStep n).2 ∧ (pellStep n).1 < (pellStep (n + 1)).1 := by
  induction n with
  | zero => refine ⟨by simp [pellStep], by simp [pellStep], by simp [pellStep]⟩
  | succ n ih =>
    obtain ⟨h1, h2, _⟩ := ih
    refine ⟨?_, ?_, ?_⟩ <;> simp only [pellStep] <;> linarith

/-- The set of integer solutions of `x² − 2·y² = 1` is infinite. -/
