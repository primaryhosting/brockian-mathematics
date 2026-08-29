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
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- written as an ordinary block comment.)

import Mathlib

/-!
## The special case of the Baker–Campbell–Hausdorff formula

If the commutator `C = A * B - B * A` commutes with both `A` and `B` (in particular if it is
central), then in a Banach algebra
`exp A * exp B = exp (A + B + ½ • (A * B - B * A))`.

Mathlib provides `NormedSpace.exp_add_of_commute` (the case `C = 0`) and the derivative
`hasDerivAt_exp_smul_const`, but not this refinement, so it is proved here by the classical
ODE argument: the function
`t ↦ exp (-(t²/2) • C) * exp (-t • (A+B)) * exp (t • A) * exp (t • B)`
has vanishing derivative, hence is constantly `1`.
-/

open NormedSpace

namespace QPhys

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]

omit [NormedAlgebra ℝ 𝔸] in
/-- Purely algebraic identity used for the derivative of the conjugation `s ↦ e^{-sA} (B + sC) e^{sA}`. -/

theorem bch_deriv_algebraic (u v w z A B C : 𝔸) (t : ℝ)
    (hCv : C * v = v * C) (hSv : (A + B) * v = v * (A + B))
    (hwB : w * B = B * w + t • (C * w)) (hzB : z * B = B * z) :
    ((((-t) • (u * C)) * v + u * (-((A + B) * v))) * w + (u * v) * (A * w)) * z
      + ((u * v) * w) * (z * B) = 0 := by
  have e1 : ((-t) • (u * C)) * v * w * z = (-t) • (u * v * (C * (w * z))) := by
    simp only [smul_mul_assoc]
    congr 1
    rw [mul_assoc u C v, hCv]
    noncomm_ring
  have e2 : u * (-((A + B) * v)) * w * z = -(u * v * (A * (w * z))) - u * v * (B * (w * z)) := by
    rw [hSv]; noncomm_ring
  have e3 : (u * v) * (A * w) * z = u * v * (A * (w * z)) := by noncomm_ring
  have e4 : ((u * v) * w) * (z * B) = u * v * (B * (w * z)) + t • (u * v * (C * (w * z))) := by
    rw [hzB]
    have h : (u * v * w) * (B * z) = (u * v) * ((w * B) * z) := by noncomm_ring
    rw [h, hwB, add_mul, smul_mul_assoc, mul_add, mul_smul_comm]
    congr 1 <;> noncomm_ring
  calc ((((-t) • (u * C)) * v + u * (-((A + B) * v))) * w + (u * v) * (A * w)) * z
        + ((u * v) * w) * (z * B)
      = ((-t) • (u * C)) * v * w * z + u * (-((A + B) * v)) * w * z + (u * v) * (A * w) * z
        + ((u * v) * w) * (z * B) := by noncomm_ring
    _ = 0 := by rw [e1, e2, e3, e4]; module

end

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

noncomputable local instance ratAlg : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸

/-- `exp (r • X) * exp (-r • X) = 1`. -/
