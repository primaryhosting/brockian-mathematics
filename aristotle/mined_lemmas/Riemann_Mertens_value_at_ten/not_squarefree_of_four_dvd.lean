/-
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Value At Ten
Category: Riemann Program
Target: Riemann.Mertens.value_at_ten
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Riemann.Mertens

open ArithmeticFunction

/-- The Mertens function `M(n) = ∑_{k=1}^{n} μ(k)`, where `μ` is the Möbius function. -/

private lemma not_squarefree_of_four_dvd {n : ℕ} (h : 4 ∣ n) : ¬ Squarefree n := by
  intro hs
  have := hs 2 (by simpa using h)
  simp at this

