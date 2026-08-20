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
theorem quadratic_reciprocity (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp₁ : Odd p := (Nat.Prime.odd_of_ne_two Fact.out) hp
  have hq₁ : Odd q := (Nat.Prime.odd_of_ne_two Fact.out) hq
  rw [odd_sub_one_div_two p hp₁, odd_sub_one_div_two q hq₁, mul_comm]
  exact legendreSym.quadratic_reciprocity hp hq hpq

end NumberTheory

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

