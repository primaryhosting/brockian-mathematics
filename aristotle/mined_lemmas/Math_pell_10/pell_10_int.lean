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

theorem pell_10_int : ∃ x y : ℤ, x ^ 2 - 10 * y ^ 2 = 1 ∧ y ≠ 0 := pell_10

end Math

