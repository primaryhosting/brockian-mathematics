/-
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` commands to precede any module docstring (`/-! ... -/`),
-- so the required header appears above as a plain block comment with identical text, and is
-- repeated verbatim as a module docstring immediately after the imports.

import Mathlib

/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- Key intermediate lemma: for an odd natural number `n`, the "half" appearing in the
exponent of quadratic reciprocity can be written either as `(n - 1) / 2` (truncated
natural subtraction) or as `n / 2`. -/

theorem odd_sub_one_div_two (n : ℕ) (hn : Odd n) : (n - 1) / 2 = n / 2 := by
  obtain ⟨k, rfl⟩ := hn
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`(p/q) * (q/p) = (-1) ^ ((p-1)/2 * (q-1)/2)`, where `(·/·)` is the Legendre symbol. -/
