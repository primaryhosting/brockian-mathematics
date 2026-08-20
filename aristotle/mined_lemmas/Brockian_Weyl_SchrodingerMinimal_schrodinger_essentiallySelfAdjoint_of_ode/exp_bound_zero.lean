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

private theorem exp_bound_zero {A C a : ℝ} (ha : 0 < a) (hA : 0 ≤ A)
    (h : ∀ t : ℝ, 0 ≤ t → A * Real.exp (a * t) ≤ C) : A = 0 := by
  by_contra hne
  have hApos : 0 < A := lt_of_le_of_ne hA (Ne.symm hne)
  have h1 : Tendsto (fun t : ℝ => a * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop ha Filter.tendsto_id
  have h2 : Tendsto (fun t : ℝ => A * Real.exp (a * t)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hApos (Real.tendsto_exp_atTop.comp h1)
  obtain ⟨t, ht, ht0⟩ := ((h2.eventually_gt_atTop C).and (eventually_ge_atTop 0)).exists
  exact absurd (h t ht0) (not_le.2 ht)

