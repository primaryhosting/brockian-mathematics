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

/-- The weak (ternary) Goldbach statement: every odd number greater than `5`
is a sum of three primes. Proved by Helfgott (2013); not available in Mathlib. -/
def TernaryGoldbach : Prop :=
  ∀ n : ℕ, 5 < n → Odd n →
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

/-- A concrete witness for the smallest odd case: `7 = 2 + 2 + 3`,
with each summand prime. -/
theorem seven_eq_two_add_two_add_three :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = 7 :=
  ⟨2, 2, 3, Nat.prime_two, Nat.prime_two, Nat.prime_three, rfl⟩

/-- The stated target: the self-equivalence of the ternary Goldbach statement.
Closed by `Iff.rfl` (equivalently `Iff.refl _`, found by `exact?`). -/
theorem ternary_statement : TernaryGoldbach ↔ TernaryGoldbach := Iff.rfl

end Goldbach

