/-
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Shor Period
Category: Frontier Qi
Target: QI.shor_period
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QI

/-- **Two distinct fractions with small denominators are far apart.**
If `s/r ≠ s'/r'` then they differ by at least `1/(r*r')`. -/

theorem shor_period_nonvacuous :
    (∀ x : ℕ, ((-1 : (ZMod 3)ˣ) : ZMod 3) ^ (x + 2) = ((-1 : (ZMod 3)ˣ) : ZMod 3) ^ x) ∧
    (∀ p : ℕ, 0 < p →
        (∀ x : ℕ, ((-1 : (ZMod 3)ˣ) : ZMod 3) ^ (x + p) = ((-1 : (ZMod 3)ˣ) : ZMod 3) ^ x) →
        2 ≤ p) ∧
    (∀ s' r' : ℕ, 0 < r' → r' ≤ 3 → Nat.Coprime s' r' →
      |((8 : ℕ) : ℝ) / ((16 : ℕ) : ℝ) - (s' : ℝ) / r'| < 1 / (2 * ((16 : ℕ) : ℝ)) → r' = 2) := by
  have h2 : orderOf (-1 : (ZMod 3)ˣ) = 2 := by
    apply orderOf_eq_prime <;> decide
  exact shor_period (N := 3) (by norm_num) (-1) 16 8 1 (by norm_num) 2 h2.symm (by norm_num)
    (by norm_num) (by norm_num)

end QI

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

