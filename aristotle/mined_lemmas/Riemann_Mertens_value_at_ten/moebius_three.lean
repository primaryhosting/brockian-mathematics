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

private lemma moebius_three : moebius 3 = -1 :=
  ArithmeticFunction.moebius_apply_prime Nat.prime_three

