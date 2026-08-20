/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Redux.LinAlg

/-- Montgomery's integrality step, whose matrix analogue is Lemma 3.2:
for every natural number `m` we have `2 * m ≤ m ^ 2 + 1`, equivalently
`(m : ℤ) ^ 2 ≥ 2 * m - 1`, which is just `(m - 1) ^ 2 ≥ 0`. -/
theorem integrality_shadow (m : Nat) :
    2 * m ≤ m ^ 2 + 1 ∧ ((m : Int) ^ 2 ≥ 2 * (m : Int) - 1) := by
  have h : ∀ n : Nat, 2 * n ≤ n ^ 2 + 1 := by
    intro n
    induction n with
    | zero => decide
    | succ k ih =>
      have hk : (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 := by
        simp [Nat.pow_succ, Nat.pow_zero, Nat.mul_add, Nat.add_mul]
        omega
      omega
  refine ⟨h m, ?_⟩
  have hc : ((m : Int)) ^ 2 = ((m ^ 2 : Nat) : Int) := by
    simp [Int.natCast_pow]
  have hm := h m
  omega

end Zeta23Redux.LinAlg

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

