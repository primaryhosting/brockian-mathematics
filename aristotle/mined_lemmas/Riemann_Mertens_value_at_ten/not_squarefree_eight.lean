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

/-- The Mertens function `M n = ∑_{k=1}^{n} μ k`, where `μ` is the Möbius function. -/

private lemma not_squarefree_eight : ¬ Squarefree 8 := by
  intro h
  have := h 2 ⟨2, by norm_num⟩
  rw [Nat.isUnit_iff] at this
  omega

