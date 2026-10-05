/-!
# Pell 8
Category: Pure Mathematics
Target: Math.pell_8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 8`.**
`x² - 8·y² = 1` has a nontrivial integer solution, i.e. one with `y ≠ 0`
(so `x ≠ ±1`): namely `(x, y) = (3, 1)`, since `9 - 8 = 1`. -/

theorem pell_8_step {x y : ℤ} (h : x ^ 2 - 8 * y ^ 2 = 1) :
    (3 * x + 8 * y) ^ 2 - 8 * (x + 3 * y) ^ 2 = 1 := by
  linear_combination h

/-- `x² - 8·y² = 1` has integer solutions with arbitrarily large `y`;
in particular it has infinitely many solutions. -/
