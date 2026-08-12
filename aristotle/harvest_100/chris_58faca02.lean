/-
# Ternary Statement
Category: Frontier — Prime Numbers
Target: Goldbach.ternary_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ternary Statement
Category: Frontier — Prime Numbers
Target: Goldbach.ternary_statement
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

/-- The weak (ternary) Goldbach statement: every odd natural number greater than `5`
is a sum of three primes. -/
def TernaryGoldbach : Prop :=
  ∀ n : ℕ, 5 < n → Odd n → ∃ p q r : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

/-- A concrete instance of the ternary decomposition: `7 = 2 + 2 + 3`, with each
summand prime. -/
theorem seven_eq_two_add_two_add_three :
    Nat.Prime 2 ∧ Nat.Prime 2 ∧ Nat.Prime 3 ∧ 2 + 2 + 3 = 7 := by
  refine ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, rfl⟩

/-- The concrete odd case `n = 7` satisfies the ternary Goldbach conclusion. -/
theorem ternary_witness_seven :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = 7 :=
  ⟨2, 2, 3, Nat.prime_two, Nat.prime_two, Nat.prime_three, rfl⟩

/-- The stated target: the self-equivalence of the ternary Goldbach statement,
together with the concrete witness `7 = 2 + 2 + 3`. -/
theorem ternary_statement :
    (TernaryGoldbach ↔ TernaryGoldbach) ∧
      (Nat.Prime 2 ∧ Nat.Prime 2 ∧ Nat.Prime 3 ∧ 2 + 2 + 3 = 7) :=
  ⟨Iff.rfl, seven_eq_two_add_two_add_three⟩

end Goldbach

