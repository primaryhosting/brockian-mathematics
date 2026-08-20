/-!
# Integrality Shadow
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.integrality_shadow
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Zeta23Redux.LinAlg

/-- **Montgomery's integrality step**, `(m - 1)^2 ≥ 0`, in its two equivalent forms:
`2 * m ≤ m ^ 2 + 1` over the naturals, and `(m : ℤ) ^ 2 ≥ 2 * m - 1` over the integers.
This is the scalar shadow of the matrix statement (Lemma 3.2). -/
theorem integrality_shadow :
    (∀ m : Nat, 2 * m ≤ m ^ 2 + 1) ∧ (∀ m : Nat, ((m : Int)) ^ 2 ≥ 2 * (m : Int) - 1) := by
  have key : ∀ m : Nat, 2 * m ≤ m ^ 2 + 1 := by
    intro m
    cases m with
    | zero => decide
    | succ n =>
      have h : (n + 1) ^ 2 = n * n + 2 * n + 1 := by
        simp [Nat.pow_succ, Nat.succ_mul, Nat.mul_succ]
        omega
      rw [h]
      omega
  refine ⟨key, fun m => ?_⟩
  have h2 : ((2 * m : Nat) : Int) ≤ ((m ^ 2 + 1 : Nat) : Int) := Int.ofNat_le.mpr (key m)
  push_cast at h2
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

