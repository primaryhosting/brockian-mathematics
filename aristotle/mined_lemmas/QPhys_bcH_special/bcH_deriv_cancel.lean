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

/-
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# The special case of the Baker–Campbell–Hausdorff formula

If the commutator `C = [A, B] = A * B - B * A` is central (it suffices that it commutes with
both `A` and `B`), then in a Banach algebra

`exp A * exp B = exp (A + B + ½ • [A, B])`.

The commuting case `[A,B] = 0` is `NormedSpace.exp_add_of_commute`; searches did not turn up
the statement below in Mathlib, so we prove it by the standard ODE argument: the curve
`t ↦ exp (tA) exp (tB) exp (-t²/2 • C) exp (-t • (A+B))` has vanishing derivative, hence is
constantly `1`.
-/

open NormedSpace

namespace QPhys

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `NormedSpace.exp_add_of_commute` for a real Banach algebra. -/

theorem bcH_deriv_cancel (A B C P Q R S : 𝔸) (s : ℝ)
    (e1 : A * Q = Q * (A + s • C)) (cRC : C * R = R * C)
    (hRA : R * (A * S) = A * (R * S)) (hRB : R * (B * S) = B * (R * S))
    (cS : (A + B) * S = S * (A + B)) :
    0 = ((P * A * Q + P * (Q * B)) * R + P * Q * (s • (R * (-C)))) * S
        + P * Q * R * (S * (-(A + B))) := by
  rw [mul_assoc P A Q, e1, mul_neg S (A + B), ← cS]
  simp only [mul_add, add_mul, mul_neg, neg_mul, mul_smul_comm, smul_mul_assoc, mul_assoc,
    ← cRC, hRA, hRB, smul_neg]
  abel

/-- The rescaled identity: `e^{tA} e^{tB} e^{-t²C/2} e^{-t(A+B)} = 1` for all real `t`. -/
