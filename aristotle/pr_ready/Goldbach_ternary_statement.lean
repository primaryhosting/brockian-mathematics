/-!
# Ternary Statement
Category: Frontier — Prime Numbers
Target: Goldbach.ternary_statement
Statement: Weak (ternary) Goldbach, proved by Helfgott (2013) but not in Mathlib: state as a Prop TernaryGoldbach := forall n : Nat, 5 < n -> Odd n -> exists p q r, Nat.Prime p and Nat.Prime q and Nat.Prime r and p+q+r = n, and prove TernaryGoldbach <-> TernaryGoldbach. Also prove the instance: 7 = 2+2+3 with each prime (a concrete odd case witness for small n).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Goldbach

/-- The weak (ternary) Goldbach conjecture, proved by Helfgott (2013), not in Mathlib:
every odd natural number greater than `5` is a sum of three primes. -/
def TernaryGoldbach : Prop :=
  ∀ n : ℕ, 5 < n → Odd n → ∃ p q r : ℕ,
    Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

/-- A concrete instance of the ternary decomposition: `7 = 2 + 2 + 3`, all three summands prime. -/
theorem seven_eq_two_add_two_add_three :
    Nat.Prime 2 ∧ Nat.Prime 2 ∧ Nat.Prime 3 ∧ 2 + 2 + 3 = 7 :=
  ⟨Nat.prime_two, Nat.prime_two, Nat.prime_three, rfl⟩

/-- The ternary decomposition property holds for `n = 7`. -/
theorem ternary_seven :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = 7 :=
  ⟨2, 2, 3, seven_eq_two_add_two_add_three⟩

/-- The target statement: the self-equivalence of the ternary Goldbach statement,
together with the concrete witness `7 = 2 + 2 + 3`. -/
theorem ternary_statement :
    (TernaryGoldbach ↔ TernaryGoldbach) ∧
      (Nat.Prime 2 ∧ Nat.Prime 2 ∧ Nat.Prime 3 ∧ 2 + 2 + 3 = 7) :=
  ⟨Iff.rfl, seven_eq_two_add_two_add_three⟩

end Goldbach

