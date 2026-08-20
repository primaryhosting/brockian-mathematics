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

theorem bcH_aux (A B : 𝔸) (hA : Commute A (A * B - B * A)) (hB : Commute B (A * B - B * A))
    (t : ℝ) :
    exp (t • A) * exp (t • B) * exp ((t ^ 2 / 2) • (-(A * B - B * A))) * exp (t • (-(A + B)))
      = 1 := by
  set C := A * B - B * A with hC
  have hd : ∀ s : ℝ, HasDerivAt
      (fun u : ℝ => exp (u • A) * exp (u • B) * exp ((u ^ 2 / 2) • (-C)) * exp (u • (-(A + B))))
      0 s := by
    intro s
    have hP : HasDerivAt (fun u : ℝ => exp (u • A)) (exp (s • A) * A) s :=
      hasDerivAt_exp_smul_const A s
    have hQ : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (s • B) * B) s :=
      hasDerivAt_exp_smul_const B s
    have hS : HasDerivAt (fun u : ℝ => exp (u • (-(A + B)))) (exp (s • (-(A + B))) * (-(A + B))) s :=
      hasDerivAt_exp_smul_const _ s
    have hu : HasDerivAt (fun u : ℝ => u ^ 2 / 2) s s := by
      simpa using ((hasDerivAt_pow 2 s).div_const 2)
    have hR : HasDerivAt (fun u : ℝ => exp ((u ^ 2 / 2) • (-C)))
        (s • (exp ((s ^ 2 / 2) • (-C)) * (-C))) s := by
      have := (hasDerivAt_exp_smul_const (-C) (s ^ 2 / 2)).scomp s hu
      simpa [Function.comp] using this
    have h := (((hP.mul hQ).mul hR).mul hS)
    convert h using 1
    simp only [Pi.mul_apply]
    have cRA : Commute (exp ((s ^ 2 / 2) • (-C))) A :=
      ((hA.neg_right.smul_right (s ^ 2 / 2)).symm).exp_left
    have cRB : Commute (exp ((s ^ 2 / 2) • (-C))) B :=
      ((hB.neg_right.smul_right (s ^ 2 / 2)).symm).exp_left
    refine bcH_deriv_cancel A B C _ _ _ _ s (mul_exp_smul A B hB s) ?_ ?_ ?_ ?_
    · exact ((((Commute.refl C).neg_right).smul_right (s ^ 2 / 2)).exp_right).eq
    · rw [← mul_assoc, cRA.eq, mul_assoc]
    · rw [← mul_assoc, cRB.eq, mul_assoc]
    · exact (((Commute.refl (A + B)).neg_right).smul_right s).exp_right.eq
  have h0 := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa using h0

/-- **Special case of the Baker–Campbell–Hausdorff formula.**  In a real Banach algebra, if the
commutator `[A, B] = A * B - B * A` commutes with both `A` and `B` (in particular if it is
central), then `e^A e^B = e^{A + B + ½ [A,B]}`. -/
