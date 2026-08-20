import Mathlib

/-!
# Quadratic Reciprocity
Category: Frontier Wave 2 (deeper machinery)
Target: NumberTheory.quadratic_reciprocity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace NumberTheory

/-- For an odd prime `p`, `(p - 1) / 2 = p / 2` (natural number division). -/
theorem sub_one_div_two_eq_div_two_of_odd_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (p - 1) / 2 = p / 2 := by
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  subst hk
  omega

/-- **Gauss's law of quadratic reciprocity**: for distinct odd primes `p` and `q`,
`legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2))`. -/
theorem quadratic_reciprocity {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym p q * legendreSym q p = (-1) ^ ((p - 1) / 2 * ((q - 1) / 2)) := by
  have h := legendreSym.quadratic_reciprocity hq hp (Ne.symm hpq)
  rw [sub_one_div_two_eq_div_two_of_odd_prime (Fact.out) hp,
    sub_one_div_two_eq_div_two_of_odd_prime (Fact.out) hq]
  rw [h, Nat.mul_comm]

end NumberTheory

