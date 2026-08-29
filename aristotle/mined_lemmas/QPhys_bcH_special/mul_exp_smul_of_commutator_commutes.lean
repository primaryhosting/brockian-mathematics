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

open NormedSpace

/-!
# Bc H Special

The special case of the Baker-Campbell-Hausdorff formula in which the commutator
`[A, B] = A * B - B * A` is central (i.e. commutes with both `A` and `B`):
`exp A * exp B = exp (A + B + ½ [A, B])`.

The setting is a Banach algebra `𝔸` over `ℝ` and `exp` is `NormedSpace.exp`.
The proof shows that `t ↦ exp (t A) exp (t B) exp (-t (A+B)) exp (-½ t² [A,B])`
has vanishing derivative, hence is constantly `1`; the key ingredient is the
commutation rule `A * exp (t B) = exp (t B) * (A + t [A, B])`.
-/

namespace QPhys

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- If the commutator `C = A*B - B*A` commutes with `B`, then `A` can be moved past
`exp (t • B)` at the cost of the correction `t • C`. -/

lemma mul_exp_smul_of_commutator_commutes (A B : 𝔸)
    (hB : Commute (A * B - B * A) B) (t : ℝ) :
    A * exp (t • B) = exp (t • B) * (A + t • (A * B - B * A)) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ ℝ 𝔸
  set C := A * B - B * A with hC
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun v : ℝ => exp (v • B) * ((A + v • C) * exp (v • (-B)))) 0 u := by
    intro u
    have hP : HasDerivAt (fun v : ℝ => exp (v • B)) (exp (u • B) * B) u :=
      hasDerivAt_exp_smul_const B u
    have hR : HasDerivAt (fun v : ℝ => exp (v • (-B))) (exp (u • (-B)) * (-B)) u :=
      hasDerivAt_exp_smul_const (-B) u
    have hQ : HasDerivAt (fun v : ℝ => A + v • C) C u := by
      simpa using ((hasDerivAt_id u).smul_const C).const_add A
    have h := hP.mul (hQ.mul hR)
    convert h using 1
    simp only [Pi.mul_apply]
    set X := exp (u • B)
    set R := exp (u • (-B))
    set Q := A + u • C with hQdef
    have hBR : B * R = R * B := ((((Commute.refl B).neg_right).smul_right u).exp_right).eq
    have hCR : C * R = R * C := (((hB.neg_right).smul_right u).exp_right).eq
    have hBQ : B * Q + C - Q * B = 0 := by
      have hCB : C * B = B * C := hB.eq
      have h0 : B * A + C - A * B = 0 := by rw [hC]; abel
      rw [hQdef]
      rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hCB]
      rw [← h0]
      abel
    have expand : X * B * (Q * R) + X * (C * R + Q * (R * (-B)))
        = X * ((B * Q + C - Q * B) * R) := by
      rw [mul_neg, ← hBR]
      noncomm_ring
    rw [expand, hBQ, zero_mul, mul_zero]
  have hconst := is_const_of_deriv_eq_zero
      (f := fun v : ℝ => exp (v • B) * ((A + v • C) * exp (v • (-B))))
      (fun u => (hderiv u).differentiableAt) (fun u => (hderiv u).deriv) t 0
  simp only [zero_smul, exp_zero, one_mul, mul_one, add_zero] at hconst
  have hinv : exp (t • (-B)) * exp (t • B) = 1 := by
    have hcomm : Commute (t • (-B)) (t • B) :=
      (((Commute.refl B).neg_left).smul_left t).smul_right t
    rw [← exp_add_of_commute hcomm]
    simp
  calc A * exp (t • B)
      = (exp (t • B) * ((A + t • C) * exp (t • (-B)))) * exp (t • B) := by rw [hconst]
    _ = exp (t • B) * ((A + t • C) * (exp (t • (-B)) * exp (t • B))) := by
        simp [mul_assoc]
    _ = exp (t • B) * (A + t • C) := by rw [hinv, mul_one]

/-- **Baker-Campbell-Hausdorff, special case with central commutator.**
In a Banach algebra over `ℝ`, if the commutator `[A, B] = A * B - B * A` commutes with
both `A` and `B`, then `exp A * exp B = exp (A + B + ½ [A, B])`. -/
