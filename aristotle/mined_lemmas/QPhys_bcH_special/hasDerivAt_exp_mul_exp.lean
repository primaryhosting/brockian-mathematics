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
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NormedSpace

namespace QPhys

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

noncomputable local instance instNormedAlgebraRatOfReal : NormedAlgebra ℚ 𝔸 :=
  NormedAlgebra.restrictScalars ℚ ℝ 𝔸

omit [CompleteSpace 𝔸] in
/-- A function `ℝ → 𝔸` with everywhere-vanishing derivative is constant. -/

theorem hasDerivAt_exp_mul_exp (A B C : 𝔸) (hC : A * B - B * A = C) (hAC : Commute A C) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp (s • A) * exp (s • B))
      ((A + B + t • C) * (exp (t • A) * exp (t • B))) t := by
  have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A t).mul
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) B t)
  have hkey : exp (t • A) * B = (B + t • C) * exp (t • A) := by
    rw [← hC] at hAC ⊢
    exact exp_smul_mul_eq A B hAC t
  have heq : (A + B + t • C) * (exp (t • A) * exp (t • B))
      = A * exp (t • A) * exp (t • B) + exp (t • A) * (B * exp (t • B)) := by
    rw [← mul_assoc (exp (t • A)) B, hkey, add_assoc, add_mul, mul_assoc A, mul_assoc (B + t • C)]
  rw [heq]
  exact h1

/-- The inverse path `t ↦ e^{-t(A+B)} e^{-t²C/2}` solves the ODE `h' = -h (A + B + tC)`. -/
