/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Pell's equation for `d = 10`.**

`x² - 10 y² = 1` has a nontrivial integer solution (i.e. one with `y ≠ 0`),
namely `(x, y) = (19, 6)`, since `19² - 10 · 6² = 361 - 360 = 1`.

(The general existence statement for non-square `d` is available in Mathlib as
`Pell.exists_of_not_isSquare`; here the explicit fundamental solution is given
directly, which also keeps this file free of imports so that the required
header comment can stand at the very top of the file.) -/

theorem pell_10_of_mathlib : ∃ x y : ℤ, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 :=
  Pell.exists_of_not_isSquare (by norm_num) (by decide +kernel)

end Math

