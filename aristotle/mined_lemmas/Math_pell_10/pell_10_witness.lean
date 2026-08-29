/-!
# Pell 10
Category: Pure Mathematics
Target: Math.pell_10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- The witness pair `(19, 6)` satisfies the Pell equation for `d = 10`:
`19² - 10 · 6² = 361 - 360 = 1`. -/

theorem pell_10_witness : (19 : Int) ^ 2 - 10 * (6 : Int) ^ 2 = 1 := by decide

/-- **Pell's equation for `d = 10`.**
`x² - 10·y² = 1` has a nontrivial integer solution, i.e. a solution with `y ≠ 0`
(so it is different from the trivial solutions `(±1, 0)`).
The fundamental solution is `(x, y) = (19, 6)`. -/
