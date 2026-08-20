/-
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
exponent of quadratic reciprocity can be written either as `(n - 1) / 2` (natural
subtraction) or as `n / 2`; these agree. -/
theorem sub_one_div_two_eq_div_two_of_odd {n : ℕ} (hn : Odd n) : (n - 1) / 2 = n / 2 := by
  obtain ⟨k, rfl⟩ := hn
  omega

/-- **Gauss's Law of Quadratic Reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have hp₁ : Odd p := (Fact.out (p := p.Prime)).odd_of_ne_two hp
  have hq₁ : Odd q := (Fact.out (p := q.Prime)).odd_of_ne_two hq
  rw [sub_one_div_two_eq_div_two_of_odd hp₁, sub_one_div_two_eq_div_two_of_odd hq₁,
    mul_comm (legendreSym p q)]
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

