/-
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Twin.conjecture_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Conjecture Statement
Category: Frontier — Prime Numbers
Target: Twin.conjecture_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Twin

/-- The twin prime conjecture, *stated only*: for every `N : ℕ` there is a prime `p > N`
such that `p + 2` is also prime. -/

def TwinPrimeConj : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2)

/-- Well-formedness / registration lemma: the stated proposition is a well-formed `Prop`,
equivalent to itself. This is deliberately **not** a proof of the twin prime conjecture. -/
