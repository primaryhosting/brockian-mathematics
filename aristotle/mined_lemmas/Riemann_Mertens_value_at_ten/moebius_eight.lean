/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Riemann.Mertens

open ArithmeticFunction

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is the Möbius function. -/

lemma moebius_eight : moebius 8 = 0 := by
  rw [show (8 : ℕ) = 2 ^ 3 by norm_num,
    moebius_apply_prime_pow (by norm_num) (by norm_num)]
  norm_num

