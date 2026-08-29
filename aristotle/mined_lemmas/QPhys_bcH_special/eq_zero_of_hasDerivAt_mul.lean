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

theorem eq_zero_of_hasDerivAt_mul (M : 𝔸) (Y : ℝ → 𝔸) (h : ∀ t, HasDerivAt Y (M * Y t) t)
    (h0 : Y 0 = 0) (t : ℝ) : Y t = 0 := by
  set H : ℝ → 𝔸 := fun u => exp ((-u) • M) * Y u with hH
  have hHd : ∀ u : ℝ, HasDerivAt H 0 u := by
    intro u
    have := (hasDerivAt_exp_neg_smul M u).mul (h u)
    have hzero : -(exp ((-u) • M) * M) * Y u + exp ((-u) • M) * (M * Y u) = 0 := by
      rw [neg_mul, mul_assoc, neg_add_cancel]
    rw [hzero] at this
    exact this
  have hconst := const_of_hasDerivAt_zero H hHd t
  have hH0 : H 0 = 0 := by simp [hH, h0]
  have hHt : exp ((-t) • M) * Y t = 0 := by rw [← hH0, ← hconst]
  calc Y t = (exp (t • M) * exp ((-t) • M)) * Y t := by
        rw [exp_smul_mul_exp_neg_smul, one_mul]
    _ = exp (t • M) * (exp ((-t) • M) * Y t) := by rw [mul_assoc]
    _ = 0 := by rw [hHt, mul_zero]

/-- If `C = [A,B]` commutes with `A`, then `e^{tA} B = (B + tC) e^{tA}`. -/
