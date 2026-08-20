import Mathlib

/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ArithmeticFunction

namespace Riemann.Mertens

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`. -/

private lemma mu_six : moebius 6 = 1 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num), mu_two, mu_three]
  norm_num

