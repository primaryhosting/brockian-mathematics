/-
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.ConeLine

/-- A prime `p` greater than `5` is not divisible by `5`, i.e. `p % 5 ≠ 0`. -/

theorem mod_five_ne_zero_of_prime {p : ℕ} (hp : Nat.Prime p) (h5 : 5 < p) : p % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 5 hdvd) with h1 | h1 <;> omega

/-- **Cousin prime roads.**  If `p` and `p + 4` are both prime and `p > 5`, then on the
five-ray wheel the pair `(p % 5, (p+4) % 5)` travels one of the roads `2 → 1`, `3 → 2`,
`4 → 3`. -/
