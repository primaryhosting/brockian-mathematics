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

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

set_option maxRecDepth 100000

namespace Brockian.ZumkellerNumbers

/-- The sum-of-divisors function `σ₁`, written directly as a sum over `Nat.divisors`. -/

theorem three_primeFactors_sharp :
    Odd 945 ∧ IsZumkeller 945 ∧ (945 : ℕ).primeFactors.card = 3 := by
  refine ⟨by decide, isZumkeller_945, ?_⟩
  have h : (945 : ℕ) = 3 ^ 3 * (5 * 7) := by norm_num
  have hpf : (945 : ℕ).primeFactors = {3, 5, 7} := by
    rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_pow _ (by norm_num),
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
      Nat.Prime.primeFactors (by norm_num)]
    rfl
  rw [hpf]
  rfl

end Brockian.ZumkellerNumbers

