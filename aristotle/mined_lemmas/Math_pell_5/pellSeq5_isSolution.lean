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

theorem pellSeq5_isSolution (n : ℕ) :
    (pellSeq5 n).1 ^ 2 - 5 * (pellSeq5 n).2 ^ 2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [pellSeq5]
    nlinarith [ih]

/-- The iterates grow: the `n`-th one has first coordinate at least `1` and second
coordinate at least `n + 4`. -/
