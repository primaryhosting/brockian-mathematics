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

private lemma mu_nine : moebius 9 = 0 := by
  refine moebius_eq_zero_of_not_squarefree fun h => ?_
  have := h 3 (by norm_num)
  simp at this

