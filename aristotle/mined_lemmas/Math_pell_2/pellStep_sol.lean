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

theorem pellStep_sol (n : ℕ) : (pellStep n).1 ^ 2 - 2 * (pellStep n).2 ^ 2 = 1 := by
  induction n with
  | zero => simp [pellStep]
  | succ n ih => rw [pellStep]; ring_nf; ring_nf at ih; linarith

