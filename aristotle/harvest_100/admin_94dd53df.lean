import Mathlib

/-!
# Instance 100
Category: Frontier — Prime Numbers
Target: Goldbach.instance_100
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

namespace Goldbach

/-- Key intermediate lemma: 47 and 53 are both prime. -/
lemma primes_47_53 : Nat.Prime 47 ∧ Nat.Prime 53 := by
  constructor <;> decide

/-- Goldbach for 100: `100 = 47 + 53` with both summands prime. -/
theorem instance_100 : Nat.Prime 47 ∧ Nat.Prime 53 ∧ 47 + 53 = 100 :=
  ⟨primes_47_53.1, primes_47_53.2, rfl⟩

/-- Goldbach's conjecture holds for `100`: it is a sum of two primes. -/
theorem exists_two_primes_add_eq_100 :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 100 :=
  ⟨47, 53, instance_100.1, instance_100.2.1, instance_100.2.2⟩

end Goldbach

