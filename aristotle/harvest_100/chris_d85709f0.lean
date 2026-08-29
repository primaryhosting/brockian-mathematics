/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses a plain block comment rather than a `/-! -/` module docstring,
-- because Lean 4 requires `import` commands to precede any doc comment.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The `K = 2` wheel class condition: a natural number is admissible as a summand in a
`K = 2` Goldbach decomposition modulo the wheel `2 * 3 = 6` exactly when it is coprime to `6`. -/
def WheelK2 (p : ℕ) : Prop := Nat.Coprime p 6

instance (p : ℕ) : Decidable (WheelK2 p) := by unfold WheelK2; infer_instance

/-- Every prime `p ≥ 5` lies in a `K = 2` wheel class, i.e. is coprime to `6`. -/
theorem wheelK2_of_prime {p : ℕ} (hp : Nat.Prime p) (h5 : 5 ≤ p) : WheelK2 p := by
  have h2 : Nat.Coprime p 2 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have h3 : Nat.Coprime p 3 := by
    refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_
    have := Nat.le_of_dvd (by norm_num) h
    omega
  show Nat.Coprime p (2 * 3)
  exact Nat.Coprime.mul_right h2 h3

/-- **Goldbach wheel, `K = 2`, modulus `947`.**
The even number `2 * 947 = 1894` is the sum of two primes, and both summands lie in the
`K = 2` wheel classes (they are coprime to `6`), and are moreover coprime to the wheel
modulus `947`. -/
theorem GoldbachWheelK2_947 :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = 2 * 947 ∧
      WheelK2 p ∧ WheelK2 q ∧ Nat.Coprime p 947 ∧ Nat.Coprime q 947 := by
  refine ⟨5, 1889, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩ <;> decide

end Brockian

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

