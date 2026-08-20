/-
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bkt Transition
Category: Frontier Phys
Target: Phys.bkt_transition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- Energy cost of a single vortex in a 2D XY model with spin stiffness `J`, in a
square sample of linear size `L` with short-distance (core) cutoff `a`:
`E = π J log (L / a)`. -/

theorem bkt_highT_free_energy_tendsto_atBot {J kB T a : ℝ} (hkB : 0 < kB) (ha : 0 < a)
    (hT : bktTemperature J kB < T) :
    Filter.Tendsto (fun L : ℝ => vortexFreeEnergy J kB T L a) Filter.atTop Filter.atBot := by
  have hc : Real.pi * J - 2 * kB * T < 0 := by
    rw [bktTemperature, div_lt_iff₀ (by positivity)] at hT
    nlinarith
  have h1 : Filter.Tendsto (fun L : ℝ => Real.log (L / a)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp (Filter.tendsto_id.atTop_div_const ha)
  simp only [vortexFreeEnergy_eq]
  exact Filter.Tendsto.const_mul_atTop_of_neg hc h1

end Phys

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

