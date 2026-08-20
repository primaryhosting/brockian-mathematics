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
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Exponential of a sum of commuting elements of a real Banach algebra. -/

theorem exp_smul_mul_eq {A B : 𝔸} (hA : Commute A (A * B - B * A)) (t : ℝ) :
    exp (t • A) * B = (B + t • (A * B - B * A)) * exp (t • A) := by
  set C := A * B - B * A with hC
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => exp (s • (-A)) * ((B + s • C) * exp (s • A))) 0 s := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => exp (s • (-A))) (exp (t • (-A)) * (-A)) t :=
      hasDerivAt_exp_smul_const (-A) t
    have h2 : HasDerivAt (fun s : ℝ => B + s • C) C t := by
      simpa using ((hasDerivAt_id t).smul_const C).const_add B
    have h3 : HasDerivAt (fun s : ℝ => exp (s • A)) (exp (t • A) * A) t :=
      hasDerivAt_exp_smul_const A t
    have h := h1.mul (h2.mul h3)
    convert h using 1
    simp only [Pi.mul_apply]
    set E := exp (t • A)
    set F := exp (t • (-A))
    have e1 : E * A = A * E := ((Commute.refl A).smul_left t).exp_left
    have e2 : C * (E * A) = A * (C * E) := by rw [e1, ← mul_assoc, ← hA.eq, mul_assoc]
    have key : F * (-A) * ((B + t • C) * E) + F * (C * E + (B + t • C) * (E * A))
        = F * ((-(A * B) + B * A + C) * E) + t • (F * (C * (E * A)) - F * (A * (C * E))) := by
      rw [e1]; noncomm_ring; module
    rw [key, e2, hC]; simp
  have hconst := is_const_of_deriv_eq_zero
    (f := fun s : ℝ => exp (s • (-A)) * ((B + s • C) * exp (s • A)))
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simp only [zero_smul, exp_zero, one_mul, mul_one] at hconst
  have h2 := congrArg (fun x => exp (t • A) * x) hconst
  simp only [← mul_assoc, exp_smul_mul_exp_neg_smul A t, one_mul] at h2
  simpa using h2.symm

/-- The auxiliary function `t ↦ exp (-(t²/2) C) exp (-t (A+B)) exp (tA) exp (tB)`
has vanishing derivative when the commutator `C = AB - BA` is central. -/
