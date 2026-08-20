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

theorem exp_conj_smul (A B : 𝔸) (hB : Commute B (A * B - B * A)) (t : ℝ) :
    exp (t • (-B)) * A * exp (t • B) = A + t • (A * B - B * A) := by
  set C := A * B - B * A with hC
  have hdF : ∀ s : ℝ, HasDerivAt (fun u : ℝ => exp (u • (-B)) * A * exp (u • B) - u • C) 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • (-B))) ((-B) * exp (s • (-B))) s :=
      hasDerivAt_exp_smul_const' (-B) s
    have h2 : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (s • B) * B) s :=
      hasDerivAt_exp_smul_const B s
    have h3 := ((h1.mul_const A).mul h2).sub ((hasDerivAt_id s).smul_const C)
    convert h3 using 1
    have hcomm1 : Commute (exp (s • (-B))) B :=
      ((((Commute.refl B).neg_right).smul_right s).symm).exp_left
    have hcomm2 : Commute (exp (s • B)) C := (hB.smul_left s).exp_left
    have h2b : exp (s • B) * B = B * exp (s • B) :=
      (((Commute.refl B).smul_left s).exp_left).eq
    have hEE : exp (s • (-B)) * exp (s • B) = 1 := by
      rw [smul_neg, exp_neg_mul_exp_self']
    have hmain : (-B) * exp (s • (-B)) * A * exp (s • B) + exp (s • (-B)) * A * (exp (s • B) * B)
        = exp (s • (-B)) * C * exp (s • B) := by
      rw [← (hcomm1.neg_right).eq, h2b, hC]
      noncomm_ring
    rw [hmain, one_smul, mul_assoc, ← hcomm2.eq, ← mul_assoc, hEE, one_mul, sub_self]
  have h0 := is_const_of_deriv_eq_zero (fun s => (hdF s).differentiableAt)
      (fun s => (hdF s).deriv) t 0
  simp only [zero_smul, sub_zero, exp_zero, one_mul, mul_one] at h0
  rw [sub_eq_iff_eq_add] at h0
  exact h0

/-- Moving `A` past `e^{tB}` when `[A,B]` commutes with `B`. -/
