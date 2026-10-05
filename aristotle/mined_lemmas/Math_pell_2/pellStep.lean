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

def pellStep : ℕ → ℤ × ℤ
  | 0 => (1, 0)
  | n + 1 => (3 * (pellStep n).1 + 4 * (pellStep n).2, 2 * (pellStep n).1 + 3 * (pellStep n).2)

