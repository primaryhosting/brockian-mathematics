/-
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Thirring Stability
Category: Frontier Physics
Target: Frontier.lieb_thirring_stability
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open MeasureTheory

/-- The Lieb–Thirring constant appearing in the kinetic energy inequality that is dual to
the Lieb–Thirring eigenvalue bound with constant `L` (in dimension `3`, exponent `γ = 1`). -/

theorem ltKineticConst_optimal {L K' : ℝ} (hL : 0 < L)
    (h : ∀ (T : ℝ),
      (∀ V : Unit → ℝ, (∀ x, 0 ≤ V x) →
        Integrable (fun x => V x * (1 : ℝ)) (Measure.dirac ()) →
        Integrable (fun x => (V x) ^ ((5 : ℝ) / 2)) (Measure.dirac ()) →
        T - ∫ x, V x * (1 : ℝ) ∂(Measure.dirac ())
          ≥ - L * ∫ x, (V x) ^ ((5 : ℝ) / 2) ∂(Measure.dirac ())) →
      T ≥ K' * ∫ _x : Unit, (1 : ℝ) ^ ((5 : ℝ) / 3) ∂(Measure.dirac ())) :
    K' ≤ ltKineticConst L := by
  have hone : (∫ _x : Unit, (1 : ℝ) ^ ((5 : ℝ) / 3) ∂(Measure.dirac ())) = 1 := by simp
  have hhyp := liebThirring_dual_hypothesis_sharp (μ := Measure.dirac ())
    (fun _ : Unit => (1 : ℝ)) (fun _ => zero_le_one) L hL Integrable.of_finite
  rw [hone] at hhyp
  have hK := h (ltKineticConst L * 1) (by simpa using hhyp)
  rw [hone] at hK
  linarith

/-- **Scalar stability step.** If the kinetic energy dominates `K * X` and the total
attraction is bounded by `C * X ^ (1/2) * N ^ (1/2)` (the scaling-correct Coulomb bound),
then the total energy is bounded below by `-C^2 N / (4K)`, i.e. linearly in the particle
number. -/
