/-
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/-` rather than `/-!` because Lean 4 does not allow a
-- module docstring to precede `import`; the exact docstring is repeated below.)

import Mathlib

/-!
# Canonical Commutator
Category: Quantum Physics
Target: QPhys.canonical_commutator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace QPhys

open SchwartzMap

/-- The function `x ↦ (x : ℂ)` has temperate growth (it is a continuous linear map). -/

theorem canonical_commutator (ℏ : ℝ) :
    ⁅positionOp, momentumOp ℏ⁆
      = (Complex.I * (ℏ : ℂ)) • (ContinuousLinearMap.id ℂ 𝓢(ℝ, ℂ)) := by
  ext f x
  have hderiv : deriv (fun y : ℝ => (y : ℂ) * f y) x = f x + (x : ℂ) * deriv (⇑f) x :=
    (hasDerivAt_mul_schwartz f x).deriv
  have hXf : ⇑(positionOp f) = fun y : ℝ => (y : ℂ) * f y := by
    funext y; simp
  simp only [Ring.lie_def, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply,
    SchwartzMap.sub_apply, momentumOp_apply, positionOp_apply, hXf, hderiv,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_id', id_eq,
    SchwartzMap.smul_apply, smul_eq_mul]
  ring

end QPhys

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

