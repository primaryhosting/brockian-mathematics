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

private lemma mu_ten : moebius 10 = 1 := by
  rw [show (10 : ℕ) = 2 * 5 by norm_num,
    isMultiplicative_moebius.map_mul_of_coprime (by norm_num), mu_two, mu_five]
  norm_num

/-- The Mertens function at `10`: `M(10) = ∑_{k=1}^{10} μ k = -1`. -/
