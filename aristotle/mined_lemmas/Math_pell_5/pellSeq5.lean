/-!
# Pell 5
Category: Pure Mathematics
Target: Math.pell_5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 5`.** The equation `x² - 5·y² = 1` has a nontrivial
integer solution, i.e. one with `y ≠ 0` (so that `x ≠ ±1`): take `(x, y) = (9, 4)`,
since `9² - 5·4² = 81 - 80 = 1`. -/

def pellSeq5 : ℕ → ℤ × ℤ
  | 0 => (9, 4)
  | n + 1 => (9 * (pellSeq5 n).1 + 20 * (pellSeq5 n).2,
      4 * (pellSeq5 n).1 + 9 * (pellSeq5 n).2)

/-- Every iterate solves the Pell equation `x² - 5·y² = 1`. -/
