/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open ArithmeticFunction

namespace Riemann.Mertens

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`. -/

private lemma moebius_nine : moebius 9 = 0 := by
  have h : (9 : ℕ) = 3 ^ 2 := by norm_num
  rw [h, ArithmeticFunction.moebius_apply_prime_pow Nat.prime_three (by norm_num)]
  norm_num

