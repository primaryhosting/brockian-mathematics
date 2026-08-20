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
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Schrodinger Essentially Self Adjoint Of Ode
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.SchrodingerMinimal.schrodinger_essentiallySelfAdjoint_of_ode
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Filter Complex
open scoped Convolution

namespace Brockian.Weyl.SchrodingerMinimal

/-! ## Test functions and the minimal Schrödinger expression -/

/-- A test function on the line: smooth with compact support. -/

private theorem integral_deriv_eq_zero {h : ℝ → ℂ} (hc : ContDiff ℝ 1 h)
    (hcs : HasCompactSupport h) : ∫ x, deriv h x = 0 := by
  have hint : Integrable (deriv h) volume := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hc.continuous_deriv le_rfl
    · exact hcs.deriv
  have h1 : (∫ x in Set.Iic (0:ℝ), deriv h x) + ∫ x in Set.Ioi (0:ℝ), deriv h x
      = ∫ x, deriv h x :=
    intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn
  rw [← h1, hcs.integral_Iic_deriv_eq hc 0, hcs.integral_Ioi_deriv_eq hc 0]
  ring

