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

/-! ## The pointwise (Young) inequality underlying stability -/

/-- The Lieb–Thirring stability constant appearing in the bound
`Kc * a ^ (5/3) - t * a ≥ - ltConst Kc * t ^ (5/2)`. -/

theorem lieb_thirring_one_particle_const {Kc : ℝ} (hKc0 : 0 ≤ Kc)
    (hKc : Kc * sobolevConst ^ 2 ≤ 1) (ψ : Space → ℂ) (h1 : ContDiff ℝ 1 ψ)
    (hcs : HasCompactSupport ψ) (hnorm : (∫ x, ‖ψ x‖ ^ 2) = 1) :
    Kc * ∫ x, (density (fun _ : Fin 1 => ψ) x) ^ (5 / 3 : ℝ) ≤ kineticEnergy ψ := by
  have h := lieb_thirring_one_particle ψ h1 hcs hnorm
  have hk0 : 0 ≤ kineticEnergy ψ := kineticEnergy_nonneg ψ
  nlinarith

/-- **Extensivity (linear lower bound in the number of nuclei).** If the localized
one-body potential satisfies `∫ W ^ (5/2) ≤ A * K` where `K` is the number of nuclei,
then the energy is bounded below by a constant times `K`, uniformly in the number of
electrons. -/
