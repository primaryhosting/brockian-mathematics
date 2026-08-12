import Mathlib

/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace NumberTheory

/-- For an odd prime `p`, `(p - 1) / 2 = p / 2` (natural number division/subtraction). -/
lemma pred_div_two_eq_div_two {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) :
    (p - 1) / 2 = p / 2 := by
  have hp₁ : p % 2 = 1 :=
    (Nat.Prime.eq_two_or_odd <| @Fact.out (Nat.Prime p) _).resolve_left hp
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have h := legendreSym.quadratic_reciprocity hq hp hpq.symm
  rw [pred_div_two_eq_div_two hp, pred_div_two_eq_div_two hq]
  rw [Nat.mul_comm]
  exact h

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

