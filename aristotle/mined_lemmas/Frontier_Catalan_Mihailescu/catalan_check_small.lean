import Mathlib
/-!
# Catalan Mihailescu
Category: Frontier — Prime Numbers
Target: Frontier.Catalan_Mihailescu
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace Frontier

/-- A *Catalan solution*: a pair of consecutive perfect powers, i.e. natural numbers with
`x ^ p = y ^ q + 1`, all of `x, y, p, q` being at least `2`. -/

theorem catalan_check_small : ∀ x < 50, ∀ p < 8, ∀ y < 50, ∀ q < 8,
    IsCatalanSolution x p y q → (x, p, y, q) = (3, 2, 2, 3) := by decide

/-! ### The target -/

/-- **Catalan–Mihăilescu: base cases and a Lean-checked reduction.**

* `9 = 3 ^ 2` and `8 = 2 ^ 3` are consecutive perfect powers;
* every solution of `x ^ p = y ^ q + 1` (with `x, y, p, q ≥ 2`) in which one of the bases
  equals `2`, or in which the exponents have a common factor, is exactly `3 ^ 2 = 2 ^ 3 + 1`;
* in the finite range `x, y < 50`, `p, q < 8` an exhaustive check confirms there is no other
  solution;
* the general statement follows once one rules out solutions with prime exponents and both
  bases at least `3`. -/
